#!/usr/bin/env python3
"""
CBB MATCHUP SCANNER
-------------------
Pulls team stat tables from TeamRankings (season / home / away / last season),
pulls the day's Division I slate from ESPN, and ranks every game by how
lopsided the Four Factors matchups are -- using each team's HOME split when
they're at home and AWAY split when they're on the road.

Usage (Terminal):
    python3 cbb_matchups.py                 # today's games
    python3 cbb_matchups.py --date 2026-11-21
    python3 cbb_matchups.py --refresh       # re-scrape even if today's data is cached
    python3 cbb_matchups.py --no-open       # don't auto-open the report

No installs needed -- standard library only.
"""

import argparse
import datetime as dt
import json
import math
import os
import re
import ssl
import sys
import time
import unicodedata
import urllib.error
import urllib.request
import webbrowser
from difflib import SequenceMatcher
from html.parser import HTMLParser

# --------------------------------------------------------------------------
# CONFIG
# --------------------------------------------------------------------------

TR_BASE = "https://www.teamrankings.com/ncaa-basketball/stat/"
ESPN_SCOREBOARD = ("https://site.api.espn.com/apis/site/v2/sports/basketball/"
                   "mens-college-basketball/scoreboard?dates={d}&groups=50&limit=500")

# Every TeamRankings stat page the script pulls (first working URL name wins).
STATS = {
    "games":     ["games-played"],
    "efg":       ["effective-field-goal-pct"],
    "opp_efg":   ["opponent-effective-field-goal-pct"],
    "tov":       ["turnovers-per-possession"],
    "opp_tov":   ["opponent-turnovers-per-possession"],
    "orb":       ["offensive-rebounding-pct"],
    "drb":       ["defensive-rebounding-pct"],
    "ftr":       ["fta-per-fga", "free-throws-attempted-per-field-goal-attempted"],
    "opp_ftr":   ["opponent-fta-per-fga", "opponent-free-throws-attempted-per-field-goal-attempted"],
    "three":     ["three-point-pct"],
    "opp_three": ["opponent-three-point-pct"],
    "three_rate": ["three-point-rate"],
    "opp_three_rate": ["opponent-three-point-rate"],
    "off_eff":   ["offensive-efficiency"],
    "def_eff":   ["defensive-efficiency"],
    "pace":      ["possessions-per-game"],
}

# Matchup factors: attacking team's OFFENSE stat vs defending team's DEFENSE stat.
# off_sign / def_sign orient each stat so that POSITIVE = good for the attacking offense.
FACTORS = [
    # key,   label,   off stat, def stat,   off_sign, def_sign, weight
    ("efg",  "eFG%",  "efg",   "opp_efg",   +1, +1, 0.40),
    ("tov",  "TOV",   "tov",   "opp_tov",   -1, -1, 0.25),
    ("orb",  "OREB",  "orb",   "drb",       +1, -1, 0.20),
    ("ftr",  "FT RATE", "ftr", "opp_ftr",   +1, +1, 0.15),
    ("three", "3PT",  "three", "opp_three", +1, +1, 0.10),  # scaled by how 3-reliant the offense is
]

MIN_SPLIT_GAMES = 3       # home/away split blended toward this season's overall numbers until a team has this many
                          # games in that split. Set to 1 to use raw splits no matter how few games.
Z_CAP = 3.0
THREE_DEF_SHRINK = 0.5    # opponent 3P% is mostly luck early on; count half of it
SLATE_TZ = os.environ.get("SLATE_TZ", "America/Chicago")  # which day counts as "today" in cloud mode
REQUEST_DELAY = 1.5       # seconds between TeamRankings requests (be polite, avoid getting blocked)

HERE = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(HERE, "data")
REPORT_DIR = os.path.join(HERE, "reports")
ALIAS_FILE = os.path.join(HERE, "team_aliases.json")

UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/130.0 Safari/537.36")


# --------------------------------------------------------------------------
# NETWORK
# --------------------------------------------------------------------------

def _ssl_context():
    try:
        import certifi  # present on many Macs; optional
        return ssl.create_default_context(cafile=certifi.where())
    except Exception:
        return ssl.create_default_context()


SSL_CTX = _ssl_context()


def fetch(url, accept="text/html"):
    req = urllib.request.Request(url, headers={
        "User-Agent": UA,
        "Accept": accept,
        "Accept-Language": "en-US,en;q=0.9",
    })
    try:
        with urllib.request.urlopen(req, timeout=30, context=SSL_CTX) as r:
            return r.read().decode("utf-8", errors="replace")
    except urllib.error.URLError as e:
        if isinstance(getattr(e, "reason", None), ssl.SSLError) or "CERTIFICATE" in str(e).upper():
            sys.exit(
                "\n[SSL error] Python can't verify certificates.\n"
                "Fix (one time): open Finder > Applications > Python 3.x and double-click\n"
                "'Install Certificates.command', then run this again.\n")
        raise


# --------------------------------------------------------------------------
# TEAMRANKINGS TABLE PARSER
# --------------------------------------------------------------------------

class TableParser(HTMLParser):
    """Collects every <table>: header texts + rows (cell texts + first team link)."""

    def __init__(self):
        super().__init__()
        self.tables = []
        self._t = None
        self._row = None
        self._cell = None
        self._href = None

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag == "table":
            self._t = {"headers": [], "rows": []}
        elif self._t is None:
            return
        elif tag == "tr":
            self._row = []
            self._href = None
        elif tag in ("td", "th"):
            self._cell = {"tag": tag, "text": ""}
        elif tag == "a" and self._row is not None and self._href is None:
            href = a.get("href", "")
            if "/team/" in href:
                self._href = href

    def handle_endtag(self, tag):
        if self._t is None:
            return
        if tag in ("td", "th") and self._cell is not None and self._row is not None:
            self._row.append(self._cell)
            self._cell = None
        elif tag == "tr" and self._row is not None:
            if self._row and all(c["tag"] == "th" for c in self._row):
                self._t["headers"] = [c["text"].strip() for c in self._row]
            elif self._row:
                self._t["rows"].append({"cells": [c["text"].strip() for c in self._row],
                                        "href": self._href})
            self._row = None
        elif tag == "table":
            self.tables.append(self._t)
            self._t = None

    def handle_data(self, data):
        if self._cell is not None:
            self._cell["text"] += data


def parse_num(s):
    if s is None:
        return None
    s = s.strip().replace("%", "").replace(",", "")
    if s in ("", "--", "-", "N/A"):
        return None
    try:
        return float(s)
    except ValueError:
        return None


def parse_tr_stat(html):
    """Returns {tr_slug: {name, cur, last3, last1, home, away}}"""
    p = TableParser()
    p.feed(html)
    table = None
    for t in p.tables:
        hdr = [h.lower() for h in t["headers"]]
        if "team" in hdr and "home" in hdr and "away" in hdr:
            table = t
            break
    if table is None:
        raise ValueError("stat table not found on page (site layout may have changed)")

    hdr = table["headers"]
    low = [h.lower() for h in hdr]
    years = [(i, int(h)) for i, h in enumerate(hdr) if re.fullmatch(r"\d{4}", h.strip())]
    years.sort(key=lambda x: x[1])
    idx = {
        "team": low.index("team"),
        "home": low.index("home"),
        "away": low.index("away"),
        "last3": low.index("last 3") if "last 3" in low else None,
        "last1": low.index("last 1") if "last 1" in low else None,
        "cur": years[-1][0] if years else None,
    }
    out = {}
    for row in table["rows"]:
        cells = row["cells"]
        if len(cells) < len(hdr):
            continue
        name = cells[idx["team"]]
        slug = None
        if row["href"]:
            slug = row["href"].rstrip("/").split("/team/")[-1].split("/")[0].split("?")[0]
        slug = slug or slugify(name)
        rec = {"name": name}
        for k in ("cur", "last3", "last1", "home", "away"):
            rec[k] = parse_num(cells[idx[k]]) if idx[k] is not None else None
        out[slug] = rec
    if not out:
        raise ValueError("stat table was empty")
    return out


# --------------------------------------------------------------------------
# DATA COLLECTION
# --------------------------------------------------------------------------

def scrape_teamrankings(date_str, refresh=False):
    os.makedirs(DATA_DIR, exist_ok=True)
    cache = os.path.join(DATA_DIR, f"tr_stats_{date_str}.json")
    if os.path.exists(cache) and not refresh:
        print(f"Using cached TeamRankings data ({os.path.basename(cache)})")
        with open(cache) as f:
            return json.load(f)

    stats, failed = {}, []
    print(f"Pulling {len(STATS)} stat pages from TeamRankings...")
    for i, (key, slugs) in enumerate(STATS.items(), 1):
        err = None
        for slug in slugs:
            try:
                stats[key] = parse_tr_stat(fetch(f"{TR_BASE}{slug}?date={date_str}"))
                print(f"  [{i:2d}/{len(STATS)}] {slug:<45} {len(stats[key])} teams")
                err = None
                break
            except Exception as e:
                err = e
            finally:
                time.sleep(REQUEST_DELAY)
        if err is not None:
            failed.append(slugs[0])
            print(f"  [{i:2d}/{len(STATS)}] {slugs[0]:<45} FAILED ({err})")

    if not stats:
        sys.exit("\nCouldn't get any TeamRankings data. If every page failed with 403, the site\n"
                 "is blocking the request -- send Claude the error output.\n")
    if failed:
        print(f"  Note: {len(failed)} stat(s) failed and will be skipped: {', '.join(failed)}")
    with open(cache, "w") as f:
        json.dump(stats, f)
    return stats


def parse_record(summary):
    m = re.match(r"\s*(\d+)-(\d+)", summary or "")
    return (int(m.group(1)) + int(m.group(2))) if m else None


def parse_home_line(odds, home_abbr, away_abbr):
    """Spread from the home team's side: -3.5 = home favored by 3.5, +3.5 = home getting 3.5."""
    if not odds:
        return None
    d = (odds.get("details") or "").strip()
    if d.upper() in ("EVEN", "PK", "PICK", "PICK'EM"):
        return 0.0
    m = re.match(r"(\S+)\s+([+-]?\d+(?:\.\d+)?)$", d)
    if m:
        abbr, val = m.group(1), float(m.group(2))
        if abbr == home_abbr:
            return val
        if abbr == away_abbr:
            return -val
    sp = odds.get("spread")
    if isinstance(sp, (int, float)):
        return float(sp)
    return None


def fetch_slate(date_str, quiet=False):
    if not quiet:
        print(f"Pulling the {date_str} slate from ESPN...")
    raw = json.loads(fetch(ESPN_SCOREBOARD.format(d=date_str.replace("-", "")), accept="application/json"))
    games = []
    for ev in raw.get("events", []):
        comp = (ev.get("competitions") or [{}])[0]
        sides = {}
        for c in comp.get("competitors", []):
            t = c.get("team", {})
            recs = {}
            for r in c.get("records", []) or []:
                typ = (r.get("type") or r.get("name") or "").lower()
                recs[typ] = r.get("summary")
            sides[c.get("homeAway")] = {
                "name": t.get("location") or t.get("shortDisplayName") or t.get("displayName"),
                "display": t.get("displayName", ""),
                "short": t.get("shortDisplayName", ""),
                "abbr": t.get("abbreviation", ""),
                "espn_slug": t.get("slug", ""),
                "record": recs.get("total") or recs.get("overall") or "",
                "g_total": parse_record(recs.get("total") or recs.get("overall")),
                "g_home": parse_record(recs.get("home")),
                "g_away": parse_record(recs.get("road") or recs.get("away")),
            }
        if "home" not in sides or "away" not in sides:
            continue
        odds = (comp.get("odds") or [{}])[0] if comp.get("odds") else {}
        stype = (ev.get("status") or {}).get("type") or {}
        scores = {}
        for c in comp.get("competitors", []):
            try:
                scores[c.get("homeAway")] = int(float(c.get("score")))
            except (TypeError, ValueError):
                pass
        games.append({
            "state": stype.get("state", ""),            # pre / in / post
            "completed": bool(stype.get("completed")),
            "status_name": stype.get("name", ""),
            "final": scores if stype.get("completed") else None,
            "home_line": parse_home_line(odds, sides["home"]["abbr"], sides["away"]["abbr"]),
            "id": ev.get("id"),
            "time": ev.get("date"),
            "status": ((ev.get("status") or {}).get("type") or {}).get("shortDetail", ""),
            "neutral": bool(comp.get("neutralSite")),
            "home": sides["home"],
            "away": sides["away"],
            "spread": odds.get("details") or "",
            "total": odds.get("overUnder"),
        })
    if not quiet:
        print(f"  {len(games)} Division I games found")
    return games


# --------------------------------------------------------------------------
# TEAM NAME MATCHING (ESPN -> TeamRankings)
# --------------------------------------------------------------------------

def slugify(s):
    s = (s or "").lower().replace("&", "").replace("'", "").replace("’", "").replace(".", "")
    return re.sub(r"[^a-z0-9]+", "-", s).strip("-")


def norm_name(s):
    s = (s or "").lower().replace("&", "").replace("'", "").replace(".", "")
    s = re.sub(r"\bstate\b", "st", s)
    s = re.sub(r"\bsaint\b", "st", s)
    s = re.sub(r"\bnorth(ern)?\b", "n", s)
    s = re.sub(r"\bsouth(ern)?\b", "s", s)
    s = re.sub(r"\beast(ern)?\b", "e", s)
    s = re.sub(r"\bwest(ern)?\b", "w", s)
    s = re.sub(r"\bcentral\b", "c", s)
    s = re.sub(r"\buniversity\b|\bof\b|\bthe\b", "", s)
    return re.sub(r"[^a-z0-9]", "", s)


# TeamRankings full team name -> the short name used in its stat tables (all 365 D1 teams).
TR_FULL_TO_SHORT = {
    "Abilene Christian Wildcats": "Abl Christian",
    "Air Force Falcons": "Air Force",
    "Akron Zips": "Akron",
    "Alabama A&M Bulldogs": "Alabama A&M",
    "Alabama Crimson Tide": "Alabama",
    "Alabama State Hornets": "Alabama St",
    "Albany Great Danes": "Albany",
    "Alcorn State Braves": "Alcorn St",
    "American Eagles": "American",
    "App State Mountaineers": "App State",
    "Arizona State Sun Devils": "Arizona St",
    "Arizona Wildcats": "Arizona",
    "Arkansas Razorbacks": "Arkansas",
    "Arkansas State Red Wolves": "Arkansas St",
    "Arkansas-Pine Bluff Golden Lions": "AR-Pine Bluff",
    "Army Black Knights": "Army",
    "Auburn Tigers": "Auburn",
    "Austin Peay Governors": "Austin Peay",
    "BYU Cougars": "BYU",
    "Ball State Cardinals": "Ball St",
    "Baylor Bears": "Baylor",
    "Bellarmine Knights": "Bellarmine",
    "Belmont Bruins": "Belmont",
    "Bethune-Cookman Wildcats": "Bethune",
    "Binghamton Bearcats": "Binghamton",
    "Boise State Broncos": "Boise St",
    "Boston College Eagles": "Boston College",
    "Boston University Terriers": "Boston U",
    "Bowling Green Falcons": "Bowling Green",
    "Bradley Braves": "Bradley",
    "Brown Bears": "Brown",
    "Bryant Bulldogs": "Bryant",
    "Bucknell Bison": "Bucknell",
    "Buffalo Bulls": "Buffalo",
    "Butler Bulldogs": "Butler",
    "Cal Poly Mustangs": "Cal Poly",
    "Cal State Bakersfield Roadrunners": "CS Bakersfield",
    "Cal State Fullerton Titans": "CS Fullerton",
    "Cal State Northridge Matadors": "CS Northridge",
    "California Baptist Lancers": "Cal Baptist",
    "California Golden Bears": "California",
    "Campbell Fighting Camels": "Campbell",
    "Canisius Golden Griffins": "Canisius",
    "Central Arkansas Bears": "C Arkansas",
    "Central Connecticut Blue Devils": "C Connecticut",
    "Central Michigan Chippewas": "C Michigan",
    "Charleston Cougars": "Charleston",
    "Charleston Southern Buccaneers": "Charleston So",
    "Charlotte 49ers": "Charlotte",
    "Chattanooga Mocs": "Chattanooga",
    "Chicago State Cougars": "Chicago St",
    "Cincinnati Bearcats": "Cincinnati",
    "Clemson Tigers": "Clemson",
    "Cleveland State Vikings": "Cleveland St",
    "Coastal Carolina Chanticleers": "Coastal Car",
    "Colgate Raiders": "Colgate",
    "Colorado Buffaloes": "Colorado",
    "Colorado State Rams": "Colorado St",
    "Columbia Lions": "Columbia",
    "Connecticut Huskies": "UConn",
    "Coppin State Eagles": "Coppin St",
    "Cornell Big Red": "Cornell",
    "Creighton Bluejays": "Creighton",
    "Dartmouth Big Green": "Dartmouth",
    "Davidson Wildcats": "Davidson",
    "Dayton Flyers": "Dayton",
    "DePaul Blue Demons": "DePaul",
    "Delaware Blue Hens": "Delaware",
    "Delaware State Hornets": "Delaware St",
    "Denver Pioneers": "Denver",
    "Detroit Mercy Titans": "Detroit Mercy",
    "Drake Bulldogs": "Drake",
    "Drexel Dragons": "Drexel",
    "Duke Blue Devils": "Duke",
    "Duquesne Dukes": "Duquesne",
    "East Carolina Pirates": "E Carolina",
    "East Tennessee State Buccaneers": "E Tennessee St",
    "East Texas A&M Lions": "E Texas A&M",
    "Eastern Illinois Panthers": "E Illinois",
    "Eastern Kentucky Colonels": "E Kentucky",
    "Eastern Michigan Eagles": "E Michigan",
    "Eastern Washington Eagles": "E Washington",
    "Elon Phoenix": "Elon",
    "Evansville Purple Aces": "Evansville",
    "Fairfield Stags": "Fairfield",
    "Fairleigh Dickinson Knights": "F Dickinson",
    "Florida A&M Rattlers": "Florida A&M",
    "Florida Atlantic Owls": "Florida Atlantic",
    "Florida Gators": "Florida",
    "Florida Gulf Coast Eagles": "FGCU",
    "Florida International Panthers": "Florida Intl",
    "Florida State Seminoles": "Florida St",
    "Fordham Rams": "Fordham",
    "Fresno State Bulldogs": "Fresno St",
    "Furman Paladins": "Furman",
    "Gardner-Webb Runnin' Bulldogs": "Gardner-Webb",
    "George Mason Patriots": "George Mason",
    "George Washington Revolutionaries": "G Washington",
    "Georgetown Hoyas": "Georgetown",
    "Georgia Bulldogs": "Georgia",
    "Georgia Southern Eagles": "Georgia So",
    "Georgia State Panthers": "Georgia St",
    "Georgia Tech Yellow Jackets": "Georgia Tech",
    "Gonzaga Bulldogs": "Gonzaga",
    "Grambling Tigers": "Grambling",
    "Grand Canyon Lopes": "Grand Canyon",
    "Green Bay Phoenix": "Green Bay",
    "Hampton Pirates": "Hampton",
    "Harvard Crimson": "Harvard",
    "Hawai'i Rainbow Warriors": "Hawai'i",
    "High Point Panthers": "High Point",
    "Hofstra Pride": "Hofstra",
    "Holy Cross Crusaders": "Holy Cross",
    "Houston Christian Huskies": "Hou Christian",
    "Houston Cougars": "Houston",
    "Howard Bison": "Howard",
    "IU Indy Jaguars": "IU Indy",
    "Idaho State Bengals": "Idaho St",
    "Idaho Vandals": "Idaho",
    "Illinois Chicago Flames": "Illinois Chicago",
    "Illinois Fighting Illini": "Illinois",
    "Illinois State Redbirds": "Illinois St",
    "Incarnate Word Cardinals": "Incarnate Word",
    "Indiana Hoosiers": "Indiana",
    "Indiana State Sycamores": "Indiana St",
    "Iona Gaels": "Iona",
    "Iowa Hawkeyes": "Iowa",
    "Iowa State Cyclones": "Iowa St",
    "Jackson State Tigers": "Jackson St",
    "Jacksonville Dolphins": "Jacksonville",
    "Jacksonville State Gamecocks": "Jacksonville St",
    "James Madison Dukes": "J Madison",
    "Kansas City Roos": "Kansas City",
    "Kansas Jayhawks": "Kansas",
    "Kansas State Wildcats": "Kansas St",
    "Kennesaw State Owls": "Kennesaw St",
    "Kent State Golden Flashes": "Kent St",
    "Kentucky Wildcats": "Kentucky",
    "LSU New Orleans Privateers": "LSU New Orleans",
    "La Salle Explorers": "La Salle",
    "Lafayette Leopards": "Lafayette",
    "Lamar Cardinals": "Lamar",
    "Le Moyne Dolphins": "Le Moyne",
    "Lehigh Mountain Hawks": "Lehigh",
    "Liberty Flames": "Liberty",
    "Lindenwood Lions": "Lindenwood",
    "Lipscomb Bisons": "Lipscomb",
    "Little Rock Trojans": "Little Rock",
    "Long Beach State Beach": "Long Beach St",
    "Long Island Sharks": "LIU",
    "Longwood Lancers": "Longwood",
    "Louisiana Ragin' Cajuns": "Louisiana",
    "Louisiana State Tigers": "LSU",
    "Louisiana Tech Bulldogs": "Louisiana Tech",
    "Louisville Cardinals": "Louisville",
    "Loyola Chicago Ramblers": "Loyola Chi",
    "Loyola Maryland Greyhounds": "Loyola MD",
    "Loyola Marymount Lions": "Loyola Mymt",
    "Maine Black Bears": "Maine",
    "Manhattan Jaspers": "Manhattan",
    "Marist Red Foxes": "Marist",
    "Marquette Golden Eagles": "Marquette",
    "Marshall Thundering Herd": "Marshall",
    "Maryland Eastern Shore Hawks": "Maryland ES",
    "Maryland Terrapins": "Maryland",
    "Massachusetts Minutemen": "UMass",
    "McNeese Cowboys": "McNeese",
    "Memphis Tigers": "Memphis",
    "Mercer Bears": "Mercer",
    "Mercyhurst Lakers": "Mercyhurst",
    "Merrimack Warriors": "Merrimack",
    "Miami (OH) RedHawks": "Miami OH",
    "Miami Hurricanes": "Miami",
    "Michigan State Spartans": "Michigan St",
    "Michigan Wolverines": "Michigan",
    "Middle Tennessee Blue Raiders": "Middle Tenn",
    "Milwaukee Panthers": "Milwaukee",
    "Minnesota Golden Gophers": "Minnesota",
    "Mississippi Rebels": "Mississippi",
    "Mississippi State Bulldogs": "Mississippi St",
    "Mississippi Valley State Delta Devils": "Miss Valley St",
    "Missouri State Bears": "Missouri St",
    "Missouri Tigers": "Missouri",
    "Monmouth Hawks": "Monmouth",
    "Montana Grizzlies": "Montana",
    "Montana State Bobcats": "Montana St",
    "Morehead State Eagles": "Morehead St",
    "Morgan State Bears": "Morgan St",
    "Mount St. Mary's Mountaineers": "Mt St Mary's",
    "Murray State Racers": "Murray St",
    "NC State Wolfpack": "NC State",
    "NJIT Highlanders": "NJIT",
    "Navy Midshipmen": "Navy",
    "Nebraska Cornhuskers": "Nebraska",
    "Nevada Wolf Pack": "Nevada",
    "New Hampshire Wildcats": "New Hampshire",
    "New Haven Chargers": "New Haven",
    "New Mexico Lobos": "New Mexico",
    "New Mexico State Aggies": "New Mexico St",
    "Niagara Purple Eagles": "Niagara",
    "Nicholls Colonels": "Nicholls",
    "Norfolk State Spartans": "Norfolk St",
    "North Alabama Lions": "N Alabama",
    "North Carolina A&T Aggies": "NC A&T",
    "North Carolina Central Eagles": "NC Central",
    "North Carolina Tar Heels": "North Carolina",
    "North Dakota Fighting Hawks": "North Dakota",
    "North Dakota State Bison": "N Dakota St",
    "North Florida Ospreys": "N Florida",
    "North Texas Mean Green": "N Texas",
    "Northeastern Huskies": "Northeastern",
    "Northern Arizona Lumberjacks": "N Arizona",
    "Northern Colorado Bears": "N Colorado",
    "Northern Illinois Huskies": "N Illinois",
    "Northern Iowa Panthers": "N Iowa",
    "Northern Kentucky Norse": "N Kentucky",
    "Northwestern State Demons": "NW State",
    "Northwestern Wildcats": "Northwestern",
    "Notre Dame Fighting Irish": "Notre Dame",
    "Oakland Golden Grizzlies": "Oakland",
    "Ohio Bobcats": "Ohio",
    "Ohio State Buckeyes": "Ohio St",
    "Oklahoma Sooners": "Oklahoma",
    "Oklahoma State Cowboys": "Oklahoma St",
    "Old Dominion Monarchs": "Old Dominion",
    "Omaha Mavericks": "Omaha",
    "Oral Roberts Golden Eagles": "Oral Roberts",
    "Oregon Ducks": "Oregon",
    "Oregon State Beavers": "Oregon St",
    "Pacific Tigers": "Pacific",
    "Penn Quakers": "Penn",
    "Penn State Nittany Lions": "Penn St",
    "Pepperdine Waves": "Pepperdine",
    "Pittsburgh Panthers": "Pittsburgh",
    "Portland Pilots": "Portland",
    "Portland State Vikings": "Portland St",
    "Prairie View A&M Panthers": "Prairie View",
    "Presbyterian Blue Hose": "Presbyterian",
    "Princeton Tigers": "Princeton",
    "Providence Friars": "Providence",
    "Purdue Boilermakers": "Purdue",
    "Purdue Fort Wayne Mastodons": "Purdue FW",
    "Queens Royals": "Queens",
    "Quinnipiac Bobcats": "Quinnipiac",
    "Radford Highlanders": "Radford",
    "Rhode Island Rams": "Rhode Island",
    "Rice Owls": "Rice",
    "Richmond Spiders": "Richmond",
    "Rider Broncs": "Rider",
    "Robert Morris Colonials": "Robert Morris",
    "Rutgers Scarlet Knights": "Rutgers",
    "SIU Edwardsville Cougars": "SIU Edward",
    "SMU Mustangs": "SMU",
    "Sacramento State Hornets": "Sacramento St",
    "Sacred Heart Pioneers": "Sacred Heart",
    "Saint Joseph's Hawks": "Saint Joseph's",
    "Saint Louis Billikens": "Saint Louis",
    "Saint Mary's Gaels": "Saint Mary's",
    "Saint Peter's Peacocks": "Saint Peter's",
    "Sam Houston Bearkats": "Sam Houston",
    "Samford Bulldogs": "Samford",
    "San Diego State Aztecs": "San Diego St",
    "San Diego Toreros": "San Diego",
    "San Francisco Dons": "San Francisco",
    "San Jose State Spartans": "San Jose St",
    "Santa Clara Broncos": "Santa Clara",
    "Seattle Redhawks": "Seattle",
    "Seton Hall Pirates": "Seton Hall",
    "Siena Saints": "Siena",
    "South Alabama Jaguars": "S Alabama",
    "South Carolina Gamecocks": "South Carolina",
    "South Carolina State Bulldogs": "S Carolina St",
    "South Carolina Upstate Spartans": "SC Upstate",
    "South Dakota Coyotes": "South Dakota",
    "South Dakota State Jackrabbits": "S Dakota St",
    "South Florida Bulls": "S Florida",
    "Southeast Missouri State Redhawks": "SE Missouri St",
    "Southeastern Louisiana Lions": "SE Louisiana",
    "Southern Illinois Salukis": "S Illinois",
    "Southern Indiana Screaming Eagles": "S Indiana",
    "Southern Jaguars": "Southern",
    "Southern Miss Golden Eagles": "Southern Miss",
    "Southern Utah Thunderbirds": "S Utah",
    "St. Bonaventure Bonnies": "St Bonaventure",
    "St. John's Red Storm": "St John's",
    "St. Thomas Tommies": "St Thomas",
    "Stanford Cardinal": "Stanford",
    "Stephen F. Austin Lumberjacks": "SF Austin",
    "Stetson Hatters": "Stetson",
    "Stonehill Skyhawks": "Stonehill",
    "Stony Brook Seawolves": "Stony Brook",
    "Syracuse Orange": "Syracuse",
    "TCU Horned Frogs": "TCU",
    "Tarleton State Texans": "Tarleton St",
    "Temple Owls": "Temple",
    "Tennessee State Tigers": "Tennessee St",
    "Tennessee Tech Golden Eagles": "Tenn Tech",
    "Tennessee Volunteers": "Tennessee",
    "Texas A&M Aggies": "Texas A&M",
    "Texas A&M-Corpus Christi Islanders": "Texas A&M-CC",
    "Texas Longhorns": "Texas",
    "Texas Southern Tigers": "Texas So",
    "Texas State Bobcats": "Texas St",
    "Texas Tech Red Raiders": "Texas Tech",
    "The Citadel Bulldogs": "The Citadel",
    "Toledo Rockets": "Toledo",
    "Towson Tigers": "Towson",
    "Troy Trojans": "Troy",
    "Tulane Green Wave": "Tulane",
    "Tulsa Golden Hurricane": "Tulsa",
    "UAB Blazers": "UAB",
    "UC Davis Aggies": "UC Davis",
    "UC Irvine Anteaters": "UC Irvine",
    "UC Riverside Highlanders": "UC Riverside",
    "UC San Diego Tritons": "UCSD",
    "UC Santa Barbara Gauchos": "UCSB",
    "UCF Knights": "UCF",
    "UCLA Bruins": "UCLA",
    "UL Monroe Warhawks": "UL Monroe",
    "UMBC Retrievers": "UMBC",
    "UMass Lowell River Hawks": "UMass Lowell",
    "UNC Asheville Bulldogs": "NC Asheville",
    "UNC Greensboro Spartans": "NC Greensboro",
    "UNC Wilmington Seahawks": "NC Wilmington",
    "UNLV Rebels": "UNLV",
    "USC Trojans": "USC",
    "UT Arlington Mavericks": "UT Arlington",
    "UT Martin Skyhawks": "UT Martin",
    "UT Rio Grande Valley Vaqueros": "UT Rio Grande",
    "UTEP Miners": "UTEP",
    "UTSA Roadrunners": "UTSA",
    "Utah State Aggies": "Utah St",
    "Utah Tech Trailblazers": "Utah Tech",
    "Utah Utes": "Utah",
    "Utah Valley Wolverines": "Utah Valley",
    "VCU Rams": "VCU",
    "VMI Keydets": "VMI",
    "Valparaiso Beacons": "Valparaiso",
    "Vanderbilt Commodores": "Vanderbilt",
    "Vermont Catamounts": "Vermont",
    "Villanova Wildcats": "Villanova",
    "Virginia Cavaliers": "Virginia",
    "Virginia Tech Hokies": "Virginia Tech",
    "Wagner Seahawks": "Wagner",
    "Wake Forest Demon Deacons": "Wake Forest",
    "Washington Huskies": "Washington",
    "Washington State Cougars": "Washington St",
    "Weber State Wildcats": "Weber St",
    "West Florida Argonauts": "W Florida",
    "West Georgia Wolves": "W Georgia",
    "West Virginia Mountaineers": "West Virginia",
    "Western Carolina Catamounts": "W Carolina",
    "Western Illinois Leathernecks": "W Illinois",
    "Western Kentucky Hilltoppers": "W Kentucky",
    "Western Michigan Broncos": "W Michigan",
    "Wichita State Shockers": "Wichita St",
    "William & Mary Tribe": "William & Mary",
    "Winthrop Eagles": "Winthrop",
    "Wisconsin Badgers": "Wisconsin",
    "Wofford Terriers": "Wofford",
    "Wright State Raiders": "Wright St",
    "Wyoming Cowboys": "Wyoming",
    "Xavier Musketeers": "Xavier",
    "Yale Bulldogs": "Yale",
    "Youngstown State Penguins": "Youngstown St"
}

# ESPN display names that differ from TeamRankings' full names.
ESPN_TO_TR_FULL = {
    "LSU Tigers": "Louisiana State Tigers", "UConn Huskies": "Connecticut Huskies",
    "Ole Miss Rebels": "Mississippi Rebels", "UIC Flames": "Illinois Chicago Flames",
    "Long Island University Sharks": "Long Island Sharks", "LIU Sharks": "Long Island Sharks",
    "UMass Minutemen": "Massachusetts Minutemen", "Pennsylvania Quakers": "Penn Quakers",
    "Seattle U Redhawks": "Seattle Redhawks", "St. Thomas-Minnesota Tommies": "St. Thomas Tommies",
    "Queens University Royals": "Queens Royals", "IU Indianapolis Jaguars": "IU Indy Jaguars",
    "SE Louisiana Lions": "Southeastern Louisiana Lions", "UAlbany Great Danes": "Albany Great Danes",
    "Texas A&M-Commerce Lions": "East Texas A&M Lions", "Florida Int'l Golden Panthers": "Florida International Panthers",
    "FIU Panthers": "Florida International Panthers", "Sam Houston State Bearkats": "Sam Houston Bearkats",
    "McNeese State Cowboys": "McNeese Cowboys", "Nicholls State Colonels": "Nicholls Colonels",
    "Grambling State Tigers": "Grambling Tigers", "Miami (FL) Hurricanes": "Miami Hurricanes",
    "Appalachian State Mountaineers": "App State Mountaineers", "Louisiana Monroe Warhawks": "UL Monroe Warhawks",
    "UT Arlington Mavericks": "UT Arlington Mavericks", "Omaha Mavericks": "Omaha Mavericks",
    "UMKC Kangaroos": "Kansas City Roos", "Kansas City Roos": "Kansas City Roos",
    "Southern Mississippi Golden Eagles": "Southern Miss Golden Eagles",
    "UNC Wilmington Seahawks": "UNC Wilmington Seahawks", "Charleston (SC) Cougars": "Charleston Cougars",
    "College of Charleston Cougars": "Charleston Cougars", "Detroit Titans": "Detroit Mercy Titans",
    "IUPUI Jaguars": "IU Indy Jaguars", "Fort Wayne Mastodons": "Purdue Fort Wayne Mastodons",
    "Saint Mary's (CA) Gaels": "Saint Mary's Gaels", "St. Joseph's Hawks": "Saint Joseph's Hawks",
}


def ascii_fold(s):
    return unicodedata.normalize("NFKD", s or "").encode("ascii", "ignore").decode()


def slugify(s):
    s = ascii_fold(s).lower().replace("&", "").replace("'", "").replace("\u2019", "").replace(".", "")
    return re.sub(r"[^a-z0-9]+", "-", s).strip("-")


def norm_name(s):
    s = ascii_fold(s).lower().replace("&", "").replace("'", "").replace("\u2019", "").replace(".", "")
    return re.sub(r"[^a-z0-9]", "", s)


class TeamMatcher:
    """ESPN team -> TeamRankings full name -> stat-table short name -> table key."""

    def __init__(self, tr_teams):
        self.tr = tr_teams                                   # table key -> short name
        self.short_to_key = {name: key for key, name in tr_teams.items()}
        self.full_norm = {norm_name(f): f for f in TR_FULL_TO_SHORT}
        self.short_norm = {norm_name(s): s for s in TR_FULL_TO_SHORT.values()}
        self.aliases = {}
        if os.path.exists(ALIAS_FILE):
            with open(ALIAS_FILE) as f:
                self.aliases = {k: v for k, v in json.load(f).items() if not k.startswith("_")}
        self.unmatched = set()

    def _key_for_short(self, short):
        return self.short_to_key.get(short) if short else None

    def match(self, side):
        disp = side["display"]
        # 1. your own overrides (value can be a TeamRankings short name like "Utah St")
        for k in (disp, side["name"], side["short"]):
            if k in self.aliases:
                hit = self._key_for_short(self.aliases[k]) or (self.aliases[k] if self.aliases[k] in self.tr else None)
                if hit:
                    return hit
        # 2. ESPN full name -> TeamRankings full name -> short name
        full = ESPN_TO_TR_FULL.get(disp, disp)
        full = full if full in TR_FULL_TO_SHORT else self.full_norm.get(norm_name(full))
        if full:
            hit = self._key_for_short(TR_FULL_TO_SHORT[full])
            if hit:
                return hit
        # 3. ESPN short/location name equals a TeamRankings short name
        for k in (side["short"], side["name"]):
            s = self.short_norm.get(norm_name(k))
            if s and self._key_for_short(s):
                return self._key_for_short(s)
        # 4. fuzzy on full name (catches small spelling differences)
        target, best, score = norm_name(disp), None, 0.0
        for f in TR_FULL_TO_SHORT:
            r = SequenceMatcher(None, target, norm_name(f)).ratio()
            if r > score:
                best, score = f, r
        if score >= 0.9 and self._key_for_short(TR_FULL_TO_SHORT[best]):
            return self._key_for_short(TR_FULL_TO_SHORT[best])
        self.unmatched.add(disp or side["name"])
        return None


# --------------------------------------------------------------------------
# SCORING
# --------------------------------------------------------------------------

def mean_sd(vals):
    vals = [v for v in vals if v is not None]
    if len(vals) < 2:
        return 0.0, 1.0
    m = sum(vals) / len(vals)
    sd = math.sqrt(sum((v - m) ** 2 for v in vals) / (len(vals) - 1)) or 1.0
    return m, sd


def build_norms(stats):
    return {key: mean_sd([r["cur"] for r in table.values()]) for key, table in stats.items()}


def blended_value(rec, context, g_split):
    """Current season only. Home/away split eases in from the overall season number until MIN_SPLIT_GAMES."""
    season = rec.get("cur")
    if season is None:
        return None, None, "no data"
    if context == "neutral":
        return season, season, "season (neutral site)"
    split_raw = rec.get(context)
    if split_raw is None or not g_split:
        return season, split_raw, f"no {context} games yet -> season #s"
    w = min(1.0, g_split / MIN_SPLIT_GAMES)
    used = w * split_raw + (1 - w) * season
    if w >= 1.0:
        return used, split_raw, f"{context} split ({g_split}g)"
    return used, split_raw, f"{context} split ({g_split}g), {int(w*100)}% split / {100-int(w*100)}% season"


def z(val, norm, sign):
    if val is None:
        return None
    m, sd = norm
    return max(-Z_CAP, min(Z_CAP, sign * (val - m) / sd))


def split_games(stats, slug, context, team):
    """Games played in this split: TeamRankings 'games played' page first, ESPN records as backup."""
    if context not in ("home", "away"):
        return None
    g = stats.get("games", {}).get(slug, {}).get(context)
    if g is not None:
        return int(round(g))
    return team["g_home"] if context == "home" else team["g_away"]


def side_value(stats, norms, stat_key, slug, context, team, sign):
    table = stats.get(stat_key)
    if not table or slug not in table:
        return None
    used, raw, note = blended_value(table[slug], context, split_games(stats, slug, context, team))
    return {"used": used, "raw": raw, "season": table[slug].get("cur"),
            "note": note, "z": z(used, norms[stat_key], sign)}


def phi(x):
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def three_volume(stats, norms, a_slug, a_ctx, a_team, d_slug, d_ctx, d_team):
    """How much the 3-point battle matters in this matchup, from 3-point attempt rates.
    Average volume -> 1.0. A low-volume shooter facing a defense that limits 3s -> near 0."""
    zs = []
    rate = side_value(stats, norms, "three_rate", a_slug, a_ctx, a_team, +1) if "three_rate" in stats else None
    allowed = side_value(stats, norms, "opp_three_rate", d_slug, d_ctx, d_team, +1) if "opp_three_rate" in stats else None
    if rate and rate["z"] is not None:
        zs.append(rate["z"])
    if allowed and allowed["z"] is not None:
        zs.append(allowed["z"])
    if not zs:
        return {"mult": 1.0, "pct": None, "rate_z": None, "allowed_z": None}
    zv = sum(zs) / len(zs)
    p = phi(zv)
    return {"mult": max(0.05, min(1.6, 2.0 * p)), "pct": p,
            "rate_z": rate["z"] if rate else None, "allowed_z": allowed["z"] if allowed else None}


def score_game(g, stats, norms, home_slug, away_slug):
    ctx_h = "neutral" if g["neutral"] else "home"
    ctx_a = "neutral" if g["neutral"] else "away"
    teams = {"home": (home_slug, ctx_h, g["home"]), "away": (away_slug, ctx_a, g["away"])}

    factors, total, wsum, biggest = [], 0.0, 0.0, None
    for key, label, off_s, def_s, off_sign, def_sign, weight in FACTORS:
        if off_s not in stats or def_s not in stats:
            continue
        dirs = {}
        for att, dfn in (("home", "away"), ("away", "home")):
            a_slug, a_ctx, a_team = teams[att]
            d_slug, d_ctx, d_team = teams[dfn]
            off = side_value(stats, norms, off_s, a_slug, a_ctx, a_team, off_sign)
            de = side_value(stats, norms, def_s, d_slug, d_ctx, d_team, def_sign)
            if not off or not de or off["z"] is None or de["z"] is None:
                dirs[att] = None
                continue
            vol = None
            if key == "three":
                # Opponent 3P% is mostly noise -> count only half of it.
                edge = off["z"] + THREE_DEF_SHRINK * de["z"]
                # Scale by how many 3s will actually be taken: attacking team's 3PA rate
                # and how many 3s the defense allows (defenses control attempts, not makes).
                vol = three_volume(stats, norms, a_slug, a_ctx, a_team, d_slug, d_ctx, d_team)
                edge *= vol["mult"]
            else:
                edge = off["z"] + de["z"]
            dirs[att] = {"off": off, "def": de, "edge": edge, "volume": vol}
            if biggest is None or abs(edge * weight) > abs(biggest["edge"] * biggest["weight"]):
                biggest = {"key": key, "label": label, "att": att, "edge": edge, "weight": weight}
        if dirs.get("home") is None or dirs.get("away") is None:
            continue
        net = dirs["home"]["edge"] - dirs["away"]["edge"]
        total += weight * net
        wsum += weight
        factors.append({"key": key, "label": label, "weight": weight, "net": net,
                        "impact": weight * net, "dirs": dirs})

    eff = None
    if "off_eff" in stats and "def_eff" in stats:
        hs = [side_value(stats, norms, "off_eff", home_slug, ctx_h, g["home"], +1),
              side_value(stats, norms, "def_eff", away_slug, ctx_a, g["away"], +1),
              side_value(stats, norms, "off_eff", away_slug, ctx_a, g["away"], +1),
              side_value(stats, norms, "def_eff", home_slug, ctx_h, g["home"], +1)]
        if all(x and x["z"] is not None for x in hs):
            eff = {"net": (hs[0]["z"] + hs[1]["z"]) - (hs[2]["z"] + hs[3]["z"]),
                   "home_off": hs[0], "away_def": hs[1], "away_off": hs[2], "home_def": hs[3]}

    pace = None
    if "pace" in stats:
        ph = side_value(stats, norms, "pace", home_slug, ctx_h, g["home"], +1)
        pa = side_value(stats, norms, "pace", away_slug, ctx_a, g["away"], +1)
        if ph and pa and ph["used"] is not None and pa["used"] is not None:
            pace = {"home": ph["used"], "away": pa["used"], "gap": abs(ph["z"] - pa["z"])}

    if not factors:
        return None
    return {"score": total / wsum if wsum else 0.0, "factors": factors, "eff": eff,
            "pace": pace, "biggest": biggest}


# --------------------------------------------------------------------------
# REPORT
# --------------------------------------------------------------------------

def slate_now():
    """Current time in the slate's time zone (matters on cloud servers, which run on UTC)."""
    try:
        from zoneinfo import ZoneInfo
        return dt.datetime.now(ZoneInfo(SLATE_TZ))
    except Exception:
        return dt.datetime.now()


def write_report(date_str, games, unmatched, skipped, failed_stats, path=None, nav=None):
    if path is None:
        os.makedirs(REPORT_DIR, exist_ok=True)
        path = os.path.join(REPORT_DIR, f"cbb_matchups_{date_str}.html")
    else:
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
    payload = {"date": date_str, "games": games, "unmatched": sorted(unmatched),
               "skipped": skipped, "failed": failed_stats, "nav": nav,
               "generated": slate_now().strftime("%b %d, %Y %I:%M %p %Z").strip()}
    data = json.dumps(payload).replace("</", "<\\/")
    html = REPORT_HTML.replace("/*__DATA__*/null", data)
    with open(path, "w") as f:
        f.write(html)
    return path


def round_floats(o):
    if isinstance(o, float):
        return round(o, 3)
    if isinstance(o, dict):
        return {k: round_floats(v) for k, v in o.items()}
    if isinstance(o, list):
        return [round_floats(v) for v in o]
    return o


REPORT_HTML = r"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>CBB Matchup Scanner</title>
<link href="https://fonts.googleapis.com/css2?family=Oswald:wght@500;600&family=DM+Mono:wght@400;500&family=DM+Sans:wght@400;500;600&display=swap" rel="stylesheet">
<style>
:root{--bg:#0a0a0d;--panel:#131318;--panel2:#18181f;--line:#26262f;--text:#ececf2;--dim:#8a8a99;
--home:#ff7a1a;--away:#22d3ee;--mono:'DM Mono',ui-monospace,monospace;--sans:'DM Sans',system-ui,sans-serif;--head:'Oswald',Impact,sans-serif}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--text);font-family:var(--sans);font-size:14px}
header{padding:22px 24px 14px;border-bottom:1px solid var(--line)}
h1{font-family:var(--head);font-weight:600;letter-spacing:.06em;margin:0;font-size:26px;text-transform:uppercase}
h1 span{color:var(--home)}
.sub{color:var(--dim);font-family:var(--mono);font-size:12px;margin-top:6px}
nav{display:flex;gap:8px;margin-top:12px}nav:empty{display:none}
nav a{color:var(--dim);text-decoration:none;border:1px solid var(--line);border-radius:999px;padding:7px 14px;font-size:13px;font-weight:500}
nav a.on{color:var(--bg);background:var(--home);border-color:var(--home)}
.scale{display:flex;gap:6px;flex-wrap:wrap;margin-top:12px;font-size:12px;color:var(--dim);align-items:center}
.controls{display:flex;flex-wrap:wrap;gap:10px;align-items:center;padding:12px 24px;border-bottom:1px solid var(--line);position:sticky;top:0;background:var(--bg);z-index:5}
.controls label{color:var(--dim);font-size:12px}
select,input[type=text]{background:var(--panel);color:var(--text);border:1px solid var(--line);border-radius:6px;padding:7px 9px;font-family:var(--sans);font-size:13px}
main{padding:16px 24px 60px;max-width:1100px}
.notes{background:var(--panel);border:1px solid var(--line);border-radius:8px;padding:10px 14px;margin-bottom:14px;font-size:12px;color:var(--dim)}
.game{background:var(--panel);border:1px solid var(--line);border-radius:12px;margin-bottom:12px;overflow:hidden}
.top{display:flex;justify-content:space-between;align-items:center;padding:10px 16px;border-bottom:1px solid var(--line);font-size:13px}
.top .m{font-weight:600}.top .meta{color:var(--dim);font-family:var(--mono);font-size:11.5px}
.body{display:grid;grid-template-columns:230px 1fr;gap:20px;padding:16px}
.verdict .lbl{font-size:11px;letter-spacing:.12em;color:var(--dim);text-transform:uppercase}
.verdict .team{font-family:var(--head);font-size:30px;line-height:1.05;letter-spacing:.02em;margin:4px 0 8px;text-transform:uppercase}
.pill{display:inline-block;font-size:11px;font-weight:600;letter-spacing:.08em;padding:4px 9px;border-radius:999px;text-transform:uppercase}
.verdict .wins{color:var(--dim);font-size:13px;margin-top:10px;line-height:1.4}
.verdict .wins b{color:var(--text)}
.battles .hdr{display:grid;grid-template-columns:150px 1fr 1fr;font-size:11px;font-weight:600;letter-spacing:.06em;text-transform:uppercase;margin-bottom:4px}
.battles .hdr .a{color:var(--away);text-align:right;padding-right:8px}.battles .hdr .h{color:var(--home);padding-left:8px}
.b{display:grid;grid-template-columns:150px 1fr 1fr;align-items:center;height:26px}
.b .name{font-size:13px;color:var(--dim)}
.b .side{height:12px;position:relative;background:#1d1d25}
.b .side.l{border-radius:6px 0 0 6px}.b .side.r{border-radius:0 6px 6px 0;border-left:1px solid #3a3a46}
.b .side i{position:absolute;top:0;height:12px}
.b .side.l i{right:0;background:var(--away);border-radius:6px 0 0 6px}.b .side.r i{left:0;background:var(--home);border-radius:0 6px 6px 0}
.cap{font-size:11px;color:var(--dim);margin-top:6px}
.why{margin-top:14px;border-top:1px solid var(--line);padding-top:12px}
.why .lbl{font-size:11px;letter-spacing:.12em;color:var(--dim);text-transform:uppercase;margin-bottom:6px}
.why li{margin:5px 0;line-height:1.45;font-size:13.5px}
.why ul{margin:0;padding-left:18px}
.tag{font-size:11px;color:var(--dim)}
.toggle{display:block;width:100%;text-align:left;background:none;border:0;border-top:1px solid var(--line);color:var(--dim);padding:8px 16px;font-size:12px;cursor:pointer;font-family:var(--sans)}
.toggle:hover{color:var(--text);background:var(--panel2)}
.detail{display:none;padding:12px 16px 16px;background:#0e0e12;overflow-x:auto}
.game.open .detail{display:block}
table{width:100%;border-collapse:collapse;font-family:var(--mono);font-size:11.5px}
th{color:var(--dim);font-weight:400;text-align:left;padding:5px 7px;border-bottom:1px solid var(--line)}
td{padding:5px 7px;border-bottom:1px solid #1c1c23;vertical-align:top}td.n{text-align:right}
.note{color:var(--dim);font-size:10.5px}.pos{color:#5ee08a}.neg{color:#ff5d6c}
.empty{color:var(--dim);padding:40px;text-align:center}
@media(max-width:760px){.body{grid-template-columns:1fr}.b,.battles .hdr{grid-template-columns:110px 1fr 1fr}}
</style></head><body>
<header><h1>CBB <span>Matchup</span> Scanner</h1><nav id="nav"></nav><div class="sub" id="sub"></div>
<div class="scale" id="scale"></div></header>
<div class="controls">
 <label>Sort</label>
 <select id="sort">
  <option value="score">Biggest overall edge</option>
  <option value="biggest">Most extreme single battle</option>
  <option value="time">Tip time</option>
 </select>
 <label>Show</label>
 <select id="min">
  <option value="0">All games</option>
  <option value="0.4" selected>Slight edge or bigger</option>
  <option value="0.8">Clear edge or bigger</option>
  <option value="1.3">Strong edge or bigger</option>
 </select>
 <input id="q" type="text" placeholder="Search team" style="width:160px">
</div>
<main id="main"></main>
<script>
const D=/*__DATA__*/null;
const $=s=>document.querySelector(s);
const TIERS=[[2.0,'Lopsided','#ff3d5a'],[1.3,'Strong edge','#ff7a1a'],[0.8,'Clear edge','#f5c542'],[0.4,'Slight edge','#9aa0b4'],[0,'Even','#4a4a58']];
const tier=v=>TIERS.find(t=>Math.abs(v)>=t[0]);
const PLAIN={efg:['Shooting','shooting','shooting defense'],tov:['Turnovers','ball security','forcing turnovers'],
 orb:['Offensive boards','offensive rebounding','defensive rebounding'],ftr:['Getting to the line','getting to the line','avoiding fouls'],
 three:['3-point shooting','3-point shooting','3-point defense']};
const f=(v,d=1)=>v==null?'--':(+v).toFixed(d);
const sgn=v=>(v>0?'+':'')+(+v).toFixed(2);
function phi(z){const t=1/(1+.2316419*Math.abs(z)),d=.3989423*Math.exp(-z*z/2);let p=d*t*(.3193815+t*(-.3565638+t*(1.781478+t*(-1.821256+t*1.330274))));return z>0?1-p:p}
function rank(q){const p=phi(q)*100;if(p>=50){const t=Math.max(1,Math.round(100-p));return t<=40?`top ${t}%`:'about average'}const b=Math.max(1,Math.round(p));return b<=40?`bottom ${b}%`:'about average'}
function timeStr(t){try{return new Date(t).toLocaleTimeString([], {hour:'numeric',minute:'2-digit'})}catch(e){return ''}}
if(D.nav)$('#nav').innerHTML=D.nav.map(n=>`<a href="${n.href}" class="${n.active?'on':''}">${n.label}</a>`).join('');
$('#sub').textContent=`${D.date} · ${D.games.length} games · updated ${D.generated}`;
$('#scale').innerHTML='Edge size: '+TIERS.slice().reverse().map(t=>`<span class="pill" style="background:${t[2]}22;color:${t[2]}">${t[1]}</span>`).join('');
function notes(){let n=[];
 if(D.failed.length)n.push(`Stats that didn't load (left out): ${D.failed.join(', ')}`);
 if(D.unmatched.length)n.push(`Not on TeamRankings (usually non-D1 opponents): ${D.unmatched.join(', ')}`);
 if(D.skipped)n.push(`${D.skipped} game(s) skipped for missing data.`);
 return n.length?`<div class="notes">${n.join('<br>')}</div>`:''}
const WORDS={ // [offense good, offense bad, defense good, defense bad]
 efg:['shoots it well','struggles to shoot','defends shots well','gives up good shots'],
 tov:['takes care of the ball','turns it over a lot','forces a lot of turnovers','rarely forces turnovers'],
 orb:['crashes the offensive glass','rarely gets offensive boards','owns the defensive glass','gives up offensive boards'],
 ftr:['gets to the line a lot','rarely gets to the line',"doesn't foul much",'fouls a lot'],
 three:['hits 3s','struggles from 3','guards the 3-point line well','gives up open 3s']};
function said(team,key,isOff,q){
 const w=WORDS[key],r=rank(q);
 if(r==='about average')return `${team} is average ${isOff?'on this end':'defending it'}`;
 return `${team} ${q>0?(isOff?w[0]:w[2]):(isOff?w[1]:w[3])} (${r})`;
}
function reasons(g){
 const nm={home:g.home.name,away:g.away.name},out=[];
 const fav=g.score>=0?'home':'away';
 const fs=g.factors.slice().sort((a,b)=>Math.abs(b.impact)-Math.abs(a.impact)).filter(x=>Math.abs(x.impact)>=0.12).slice(0,3);
 for(const fc of fs){
  const winner=fc.net>=0?'home':'away',loser=winner==='home'?'away':'home';
  const wOff=fc.dirs[winner],lOff=fc.dirs[loser];
  // which half drives it: winner's offense vs loser's D, or winner's D vs loser's offense
  const s=(wOff.edge>=-lOff.edge)
   ? `<b>${said(nm[winner],fc.key,true,wOff.off.z)}</b>, and ${said(nm[loser],fc.key,false,-wOff.def.z)}.`
   : `<b>${said(nm[winner],fc.key,false,-lOff.def.z)}</b>, and ${said(nm[loser],fc.key,true,lOff.off.z)}.`;
  let volNote='';
  if(fc.key==='three'){
   const drv=(wOff.edge>=-lOff.edge)?wOff:lOff, shooter=(wOff.edge>=-lOff.edge)?nm[winner]:nm[loser];
   const v=drv.volume;
   if(v&&v.pct!=null&&v.mult<0.35)continue;            // barely any 3s in this matchup: not worth listing
   if(v&&v.pct!=null&&v.mult<0.8)volNote=` <span class="tag">(${shooter} doesn't take many 3s here, so this counts for less)</span>`;
   else if(v&&v.pct!=null&&v.mult>1.25)volNote=` <span class="tag">(${shooter} lives behind the arc, so this one matters more)</span>`;
  }
  const against=winner!==fav?` <span class="tag">(this one goes the other way)</span>`:'';
  out.push(`<li><span style="color:var(--${winner})">${PLAIN[fc.key][0]}:</span> ${s}${volNote}${against}</li>`);
 }
 if(!out.length)out.push('<li>No single battle stands out. These teams match up evenly.</li>');
 return out.join('');
}
function battles(g){
 const MAX=1.2; // impact (stat gap x importance) that fills the whole bar
 return `<div class="hdr"><span></span><span class="a">◀ ${g.away.name}</span><span class="h">${g.home.name} ▶</span></div>`+
  g.factors.map(fc=>{const w=Math.min(100,Math.abs(fc.impact)/MAX*100),h=fc.impact>=0;
   return `<div class="b"><span class="name">${PLAIN[fc.key][0]}</span>
    <span class="side l">${!h?`<i style="width:${w}%"></i>`:''}</span><span class="side r">${h?`<i style="width:${w}%"></i>`:''}</span></div>`}).join('')+
  `<div class="cap">Bar length = how much that battle swings the game (size of the gap × how much it matters)</div>`;
}
function detail(g){
 const name={home:g.home.name,away:g.away.name};let rows='';
 for(const fc of g.factors){for(const att of ['home','away']){const d=fc.dirs[att],dfn=att==='home'?'away':'home';
  rows+=`<tr><td>${att==='home'?`<b>${PLAIN[fc.key][0]}</b>`:''}</td>
   <td style="color:var(--${att})">${name[att]} offense</td><td class="n">${f(d.off.used,3)}</td><td class="n">${f(d.off.z,2)}</td>
   <td><span class="note">${d.off.note}${d.volume?` · 3PA volume x${f(d.volume.mult,2)}, opp 3P% counted at half`:''}</span></td>
   <td style="color:var(--${dfn})">${name[dfn]} defense</td><td class="n">${f(d.def.used,3)}</td><td class="n">${f(d.def.z,2)}</td>
   <td><span class="note">${d.def.note}</span></td><td class="n ${d.edge>=0?'pos':'neg'}">${sgn(d.edge)}</td></tr>`}}
 let extra='';
 if(g.eff)extra+=`<div class="note" style="margin-top:10px">Points per possession: ${g.home.name} O ${f(g.eff.home_off.used,3)} vs ${g.away.name} D ${f(g.eff.away_def.used,3)} · ${g.away.name} O ${f(g.eff.away_off.used,3)} vs ${g.home.name} D ${f(g.eff.home_def.used,3)}</div>`;
 if(g.pace)extra+=`<div class="note">Pace: ${g.home.name} ${f(g.pace.home)} poss/game · ${g.away.name} ${f(g.pace.away)} poss/game</div>`;
 return `<table><tr><th>Battle</th><th>Offense</th><th class="n">value</th><th class="n">z</th><th>based on</th><th>Defense</th><th class="n">value</th><th class="n">z</th><th>based on</th><th class="n">edge</th></tr>${rows}</table>${extra}
 <div class="note" style="margin-top:8px">z = how far from the D1 average in standard deviations (+ = good for that offense). Edge = offense z + defense z. Impact on the verdict = edge gap × the battle's weight (shooting 40%, turnovers 25%, boards 20%, free throws 15%, 3s 10%).</div>`;
}
function card(g,i){
 const fav=g.score>=0?'home':'away',t=tier(g.score),team=fav==='home'?g.home.name:g.away.name;
 const won=g.factors.filter(fc=>(fc.net>=0)===(fav==='home')&&Math.abs(fc.net)>=0.3).length;
 const eff=g.eff?`<br>${(g.eff.net>=0)===(fav==='home')?'Also scores more efficiently and defends better overall.':'But the other team is more efficient overall, so be careful.'}`:'';
 const head=t[1]==='Even'?`<div class="team" style="color:var(--dim)">Even</div>`:`<div class="team" style="color:var(--${fav})">${team}</div>`;
 return `<div class="game"><div class="top"><span class="m"><span style="color:var(--away)">${g.away.name}</span> ${g.neutral?'vs':'@'} <span style="color:var(--home)">${g.home.name}</span></span>
  <span class="meta">#${i+1} · ${timeStr(g.time)}${g.neutral?' · neutral site':''}${g.spread?' · '+g.spread:''}${g.total?' · O/U '+g.total:''}</span></div>
 <div class="body"><div class="verdict"><div class="lbl">Matchup edge</div>${head}
   <span class="pill" style="background:${t[2]}22;color:${t[2]}">${t[1]}</span>
   <div class="wins">${t[1]==='Even'?'Neither team has a real advantage.':(won*2>g.factors.length?`Wins <b>${won} of ${g.factors.length}</b> battles.`:`Wins only <b>${won} of ${g.factors.length}</b> battles, but by bigger margins.`)}${t[1]==='Even'?'':eff}</div></div>
  <div><div class="battles">${battles(g)}</div><div class="why"><div class="lbl">Why</div><ul>${reasons(g)}</ul></div></div></div>
 <button class="toggle" onclick="this.parentNode.classList.toggle('open')">Show the math ▾</button>
 <div class="detail">${detail(g)}</div></div>`;
}
function render(){
 const sort=$('#sort').value,min=+$('#min').value,q=$('#q').value.toLowerCase();
 let gs=D.games.filter(g=>Math.abs(g.score)>=min&&(!q||(g.home.name+' '+g.away.name+' '+g.home.display+' '+g.away.display).toLowerCase().includes(q)));
 const key={score:g=>-Math.abs(g.score),biggest:g=>-Math.abs(g.biggest?g.biggest.edge:0),time:g=>new Date(g.time).getTime()}[sort];
 gs.sort((a,b)=>key(a)-key(b));
 $('#main').innerHTML=notes()+(gs.length?gs.map(card).join(''):'<div class="empty">No games match. Try "All games".</div>');
}
['#sort','#min','#q'].forEach(s=>$(s).addEventListener('input',render));
render();
</script></body></html>"""


RECORD_HTML = r"""<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>CBB Matchup Scanner · Record</title>
<link href="https://fonts.googleapis.com/css2?family=Oswald:wght@500;600&family=DM+Mono:wght@400;500&family=DM+Sans:wght@400;500;600&display=swap" rel="stylesheet">
<style>
:root{--bg:#0a0a0d;--panel:#131318;--line:#26262f;--text:#ececf2;--dim:#8a8a99;--home:#ff7a1a;--away:#22d3ee;
--good:#5ee08a;--bad:#ff5d6c;--mono:'DM Mono',ui-monospace,monospace;--sans:'DM Sans',system-ui,sans-serif;--head:'Oswald',Impact,sans-serif}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--text);font-family:var(--sans);font-size:14px}
header{padding:22px 24px 14px;border-bottom:1px solid var(--line)}
h1{font-family:var(--head);font-weight:600;letter-spacing:.06em;margin:0;font-size:26px;text-transform:uppercase}h1 span{color:var(--home)}
nav{display:flex;gap:8px;margin-top:12px;flex-wrap:wrap}
nav a{color:var(--dim);text-decoration:none;border:1px solid var(--line);border-radius:999px;padding:7px 14px;font-size:13px;font-weight:500}
nav a.on{color:var(--bg);background:var(--home);border-color:var(--home)}
.sub{color:var(--dim);font-family:var(--mono);font-size:12px;margin-top:10px}
main{padding:16px 24px 60px;max-width:1000px}
.period{display:flex;gap:6px;margin-bottom:16px}
.period button{background:var(--panel);color:var(--dim);border:1px solid var(--line);border-radius:6px;padding:7px 12px;font-family:var(--sans);font-size:13px;cursor:pointer}
.period button.on{color:var(--text);border-color:var(--text)}
.cards{display:grid;grid-template-columns:repeat(auto-fit,minmax(200px,1fr));gap:12px;margin-bottom:18px}
.card{background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:14px 16px}
.card .lbl{font-size:11px;letter-spacing:.12em;color:var(--dim);text-transform:uppercase}
.card .big{font-family:var(--head);font-size:34px;margin-top:4px}
.card .small{color:var(--dim);font-size:12.5px;margin-top:2px}
h2{font-family:var(--head);font-weight:500;letter-spacing:.06em;text-transform:uppercase;font-size:17px;margin:22px 0 4px}
.hint{color:var(--dim);font-size:12.5px;margin-bottom:8px;line-height:1.45}
table{width:100%;border-collapse:collapse;background:var(--panel);border:1px solid var(--line);border-radius:10px;overflow:hidden}
th{color:var(--dim);font-weight:500;font-size:11.5px;text-align:left;padding:9px 12px;border-bottom:1px solid var(--line);text-transform:uppercase;letter-spacing:.06em}
td{padding:9px 12px;border-bottom:1px solid #1c1c23;font-size:13.5px}
td.n,th.n{text-align:right;font-family:var(--mono)}
.good{color:var(--good)}.bad{color:var(--bad)}.dim{color:var(--dim)}
.pill{display:inline-block;font-size:10.5px;font-weight:600;letter-spacing:.06em;padding:3px 8px;border-radius:999px;text-transform:uppercase}
.empty{background:var(--panel);border:1px solid var(--line);border-radius:12px;padding:30px;text-align:center;color:var(--dim);line-height:1.6}
.wrap{overflow-x:auto}
</style></head><body>
<header><h1>CBB <span>Matchup</span> Scanner</h1><nav id="nav"></nav><div class="sub" id="sub"></div></header>
<main id="main"></main>
<script>
const D=/*__DATA__*/null;
const $=s=>document.querySelector(s);
const TIERS=[['Lopsided','#ff3d5a'],['Strong edge','#ff7a1a'],['Clear edge','#f5c542'],['Slight edge','#9aa0b4'],['Even','#6a6a78']];
const tcol=t=>(TIERS.find(x=>x[0]===t)||['','#888'])[1];
const BREAKEVEN=52.4;
$('#nav').innerHTML=(D.nav||[]).map(n=>`<a href="${n.href}" class="${n.active?'on':''}">${n.label}</a>`).join('');
$('#sub').textContent=`updated ${D.generated} · ${D.pending} pick(s) waiting on results`;
let period='all';
function inPeriod(p){if(period==='all')return true;const days=period==='7'?7:30;
 const d=new Date(p.date+'T12:00:00'),cut=new Date();cut.setDate(cut.getDate()-days);return d>=cut}
function tally(ps){const r={n:ps.length,suW:0,suL:0,aW:0,aL:0,aP:0};
 for(const p of ps){p.result.su==='W'?r.suW++:r.suL++;const a=p.result.ats;if(a==='W')r.aW++;else if(a==='L')r.aL++;else if(a==='P')r.aP++}return r}
const pct=(w,l)=>w+l?(100*w/(w+l)):null;
const fp=v=>v==null?'—':v.toFixed(1)+'%';
function suCell(r){const v=pct(r.suW,r.suL);return `${r.suW}-${r.suL} <span class="dim">${fp(v)}</span>`}
function atsCell(r){const v=pct(r.aW,r.aL),c=v==null?'dim':v>=BREAKEVEN?'good':'bad';
 return `${r.aW}-${r.aL}${r.aP?'-'+r.aP:''} <span class="${c}">${fp(v)}</span>`}
const isDog=p=>p.home_line!=null&&((p.pick==='home'&&p.home_line>0)||(p.pick==='away'&&p.home_line<0));
const isFav=p=>p.home_line!=null&&((p.pick==='home'&&p.home_line<0)||(p.pick==='away'&&p.home_line>0));
function pickLine(p){if(p.home_line==null)return '—';const v=p.pick==='home'?p.home_line:-p.home_line;return v===0?'PK':(v>0?'+':'')+v}
const mark=v=>v==='W'?'<span class="good">✓</span>':v==='L'?'<span class="bad">✗</span>':v==='P'?'<span class="dim">push</span>':'<span class="dim">—</span>';
function render(){
 const ps=D.picks.filter(inPeriod);
 const per=`<div class="period">${[['all','All time'],['30','Last 30 days'],['7','Last 7 days']].map(([k,l])=>`<button class="${k===period?'on':''}" onclick="period='${k}';render()">${l}</button>`).join('')}</div>`;
 if(!ps.length){$('#main').innerHTML=per+`<div class="empty">No finished games graded yet.<br>Every game gets a saved pick before tip-off, and the next run after it ends grades it here.</div>`;return}
 const t=tally(ps),ats=pct(t.aW,t.aL);
 let h=per+`<div class="cards">
  <div class="card"><div class="lbl">Straight up</div><div class="big">${t.suW}-${t.suL}</div><div class="small">${fp(pct(t.suW,t.suL))} winners picked</div></div>
  <div class="card"><div class="lbl">Against the spread</div><div class="big ${ats==null?'':ats>=BREAKEVEN?'good':'bad'}">${t.aW}-${t.aL}${t.aP?'-'+t.aP:''}</div><div class="small">${fp(ats)} · ${BREAKEVEN}% needed to profit at -110</div></div>
  <div class="card"><div class="lbl">Games graded</div><div class="big">${t.n}</div><div class="small">${D.pending} waiting on results</div></div></div>`;
 h+=`<h2>By edge size</h2><div class="hint">If the scoring is measuring something real, bigger edges should win and cover more often than smaller ones.</div>
 <div class="wrap"><table><tr><th>Edge</th><th class="n">Games</th><th class="n">Straight up</th><th class="n">Against spread</th></tr>`+
 TIERS.map(([name,col])=>{const sub=ps.filter(p=>p.tier===name);if(!sub.length)return '';const r=tally(sub);
  return `<tr><td><span class="pill" style="background:${col}22;color:${col}">${name}</span></td><td class="n">${r.n}</td><td class="n">${suCell(r)}</td><td class="n">${atsCell(r)}</td></tr>`}).join('')+`</table></div>`;
 const dog=ps.filter(isDog),fav=ps.filter(isFav);
 h+=`<h2>Scanner vs. Vegas</h2><div class="hint">Games where the scanner's pick is the betting underdog are where it disagrees with the line. That's where a real edge would show up.</div>
 <div class="wrap"><table><tr><th>Scanner's pick was…</th><th class="n">Games</th><th class="n">Straight up</th><th class="n">Against spread</th></tr>
 ${[['The betting favorite',fav],['The betting underdog',dog]].map(([l,s])=>{const r=tally(s);return `<tr><td>${l}</td><td class="n">${r.n}</td><td class="n">${r.n?suCell(r):'—'}</td><td class="n">${r.n?atsCell(r):'—'}</td></tr>`}).join('')}</table></div>`;
 h+=`<h2>Results</h2><div class="wrap"><table><tr><th>Date</th><th>Game</th><th>Pick</th><th class="n">Line</th><th class="n">Final</th><th class="n">SU</th><th class="n">ATS</th></tr>`+
  ps.slice(0,150).map(p=>{const r=p.result,col=tcol(p.tier);
   return `<tr><td class="dim">${p.date.slice(5)}</td><td>${p.away} ${p.neutral?'vs':'@'} ${p.home}</td>
   <td><b style="color:${p.pick==='home'?'var(--home)':'var(--away)'}">${p.pick_team}</b> <span class="pill" style="background:${col}22;color:${col}">${p.tier}</span></td>
   <td class="n">${pickLine(p)}</td><td class="n">${r.away}-${r.home}</td><td class="n">${mark(r.su)}</td><td class="n">${mark(r.ats)}</td></tr>`}).join('')+`</table></div>`;
 $('#main').innerHTML=h;
}
render();
</script></body></html>"""


# --------------------------------------------------------------------------
# MAIN
# --------------------------------------------------------------------------

def run(date_str, refresh=False, open_report=True, stats=None, slate=None, out_path=None, nav=None,
        collector=None):
    stats = stats if stats is not None else scrape_teamrankings(date_str, refresh)
    failed_stats = [STATS[k][0] for k in STATS if k not in stats]
    norms = build_norms(stats)

    tr_names = {}
    for table in stats.values():
        for slug, rec in table.items():
            tr_names.setdefault(slug, rec["name"])
    matcher = TeamMatcher(tr_names)

    slate = slate if slate is not None else fetch_slate(date_str)
    out, skipped = [], 0
    for g in slate:
        hs, as_ = matcher.match(g["home"]), matcher.match(g["away"])
        if not hs or not as_:
            skipped += 1
            continue
        res = score_game(g, stats, norms, hs, as_)
        if not res:
            skipped += 1
            continue
        g["home"]["name"] = tr_names.get(hs, g["home"]["name"])
        g["away"]["name"] = tr_names.get(as_, g["away"]["name"])
        g.update(res)
        out.append(round_floats(g))

    out.sort(key=lambda g: -abs(g["score"]))
    if collector is not None:
        collector.extend(out)
    path = write_report(date_str, out, matcher.unmatched, skipped, failed_stats, out_path, nav)

    print(f"\nScored {len(out)} games ({skipped} skipped). Top 5 most lopsided:")
    for g in out[:5]:
        side = g["home"]["name"] if g["score"] >= 0 else g["away"]["name"]
        print(f"  {g['away']['name']:>18} {'vs' if g['neutral'] else '@'} {g['home']['name']:<18}"
              f"  edge: {side} {abs(g['score']):.2f}")
    print(f"\nReport: {path}")
    if open_report:
        webbrowser.open("file://" + path)
    return path


# --------------------------------------------------------------------------
# RESULTS TRACKING (cloud mode)
# --------------------------------------------------------------------------

HISTORY_FILE = os.path.join(HERE, "history", "picks.json")
TIERS_PY = [(2.0, "Lopsided"), (1.3, "Strong edge"), (0.8, "Clear edge"), (0.4, "Slight edge"), (0.0, "Even")]


def tier_of(score):
    return next(name for cut, name in TIERS_PY if abs(score) >= cut)


def load_history():
    if os.path.exists(HISTORY_FILE):
        with open(HISTORY_FILE) as f:
            return json.load(f)
    return {"picks": {}}


def save_history(hist):
    os.makedirs(os.path.dirname(HISTORY_FILE), exist_ok=True)
    with open(HISTORY_FILE, "w") as f:
        json.dump(hist, f, indent=1, sort_keys=True)


def record_picks(hist, games, date_str):
    """Save/refresh the pick for every game that hasn't tipped yet. The last pre-game run wins,
    so the record uses the latest stats and the closest line we saw before tip-off."""
    n = 0
    for g in games:
        if g.get("state", "pre") != "pre" or not g.get("id"):
            continue
        old = hist["picks"].get(g["id"])
        if old and old.get("result"):
            continue
        side = "home" if g["score"] >= 0 else "away"
        hist["picks"][g["id"]] = {
            "id": g["id"], "date": date_str, "time": g.get("time"), "neutral": g.get("neutral", False),
            "home": g["home"]["name"], "away": g["away"]["name"],
            "pick": side, "pick_team": g[side]["name"], "score": round(abs(g["score"]), 3),
            "tier": tier_of(g["score"]), "home_line": g.get("home_line"),
            "spread": g.get("spread", ""), "total": g.get("total"),
        }
        n += 1
    return n


def grade_picks(hist, today, slate_cache):
    """Fill in final scores, straight-up and against-the-spread results."""
    pending = {}
    for p in hist["picks"].values():
        if not p.get("result") and dt.date.fromisoformat(p["date"]) <= today:
            pending.setdefault(p["date"], []).append(p)
    graded = 0
    for day, picks in sorted(pending.items()):
        try:
            games = slate_cache.get(day) or fetch_slate(day, quiet=True)
        except Exception as e:
            print(f"  couldn't fetch results for {day}: {e}")
            continue
        by_id = {g["id"]: g for g in games}
        for p in picks:
            g = by_id.get(p["id"])
            old = (today - dt.date.fromisoformat(day)).days > 3
            if g is None:
                if old:
                    p["result"] = {"void": True}
                continue
            name = (g.get("status_name") or "").upper()
            if any(w in name for w in ("POSTPONED", "CANCELED", "CANCELLED", "FORFEIT")):
                p["result"] = {"void": True}
                continue
            fin = g.get("final")
            if not g.get("completed") or not fin or "home" not in fin or "away" not in fin:
                if old:
                    p["result"] = {"void": True}
                continue
            margin = fin["home"] - fin["away"]
            su = "W" if (margin > 0) == (p["pick"] == "home") else "L"
            ats = None
            if p.get("home_line") is not None:
                adj = margin + p["home_line"]
                if adj == 0:
                    ats = "P"
                else:
                    ats = "W" if (adj > 0) == (p["pick"] == "home") else "L"
            p["result"] = {"home": fin["home"], "away": fin["away"], "su": su, "ats": ats}
            graded += 1
    print(f"Graded {graded} finished game(s).")


def write_record_page(path, hist, nav):
    picks = [p for p in hist["picks"].values() if p.get("result") and not p["result"].get("void")]
    pending = sum(1 for p in hist["picks"].values() if not p.get("result"))
    payload = {"picks": sorted(picks, key=lambda p: (p["date"], p.get("time") or ""), reverse=True),
               "pending": pending, "nav": nav,
               "generated": slate_now().strftime("%b %d, %Y %I:%M %p %Z").strip()}
    html = RECORD_HTML.replace("/*__DATA__*/null", json.dumps(payload).replace("</", "<\\/"))
    with open(path, "w") as f:
        f.write(html)


def build_site(out_dir, refresh=True):
    """Cloud mode: today + tomorrow reports, pick tracking, and a Record page."""
    import copy
    os.makedirs(out_dir, exist_ok=True)
    today = slate_now().date()
    days = [("Today", today, "index.html"), ("Tomorrow", today + dt.timedelta(days=1), "tomorrow.html")]
    tabs = [(f"{l} · {d.strftime('%a %b %-d')}", f) for l, d, f in days] + [("Record", "record.html")]

    def nav_for(fname):
        return [{"label": lab, "href": f, "active": f == fname} for lab, f in tabs]

    hist, slate_cache = load_history(), {}
    for label, day, fname in days:
        print(f"\n===== {label}: {day.isoformat()} =====")
        slate = fetch_slate(day.isoformat())
        slate_cache[day.isoformat()] = copy.deepcopy(slate)
        scored = []
        run(day.isoformat(), refresh=refresh, open_report=False, slate=slate,
            out_path=os.path.join(out_dir, fname), nav=nav_for(fname), collector=scored)
        print(f"Saved {record_picks(hist, scored, day.isoformat())} pre-game pick(s).")

    print("\n===== Grading =====")
    grade_picks(hist, today, slate_cache)
    save_history(hist)
    write_record_page(os.path.join(out_dir, "record.html"), hist, nav_for("record.html"))
    open(os.path.join(out_dir, ".nojekyll"), "w").close()


def main():
    ap = argparse.ArgumentParser(description="College basketball matchup scanner")
    ap.add_argument("--date", default=dt.date.today().isoformat(), help="YYYY-MM-DD (default: today)")
    ap.add_argument("--tomorrow", action="store_true", help="scan tomorrow's slate")
    ap.add_argument("--refresh", action="store_true", help="re-scrape TeamRankings even if cached")
    ap.add_argument("--no-open", action="store_true", help="don't open the report in the browser")
    ap.add_argument("--site", metavar="DIR", help="cloud mode: build today + tomorrow pages into DIR")
    a = ap.parse_args()
    if a.site:
        build_site(a.site, refresh=True)
        return
    if a.tomorrow:
        a.date = (dt.date.today() + dt.timedelta(days=1)).isoformat()
    try:
        dt.date.fromisoformat(a.date)
    except ValueError:
        sys.exit("--date must look like 2026-11-21")
    run(a.date, refresh=a.refresh, open_report=not a.no_open)


if __name__ == "__main__":
    main()
