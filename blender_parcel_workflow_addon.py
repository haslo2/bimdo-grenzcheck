bl_info = {
    "name": "Parcel GPKG Workflow",
    "author": "OpenAI Codex",
    "version": (1, 0, 0),
    "blender": (3, 6, 0),
    "location": "View3D > Sidebar > Parcel",
    "description": "Convert a GeoPackage to GeoJSON, import it, and focus the parcel in Blender",
    "category": "Import-Export",
}

import array as _array_mod
import json
import math
import os
import re
import sqlite3
import struct
import shutil
import subprocess
import sys
import tempfile
import textwrap
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
import xml.etree.ElementTree as ET
import zipfile
import zlib
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from pathlib import Path
from typing import Any

import bpy
import bmesh
from bpy.props import BoolProperty, EnumProperty, FloatProperty, PointerProperty, StringProperty
from bpy.types import Operator, Panel, PropertyGroup
from mathutils import Vector
from mathutils.geometry import convex_hull_2d

try:
    from pyproj import Transformer
except Exception:
    Transformer = None


_zone_cache: list[tuple[str, str, str]] = [("NONE", "Keine Zonen geladen", "")]


def update_zone_cache(zones: list[dict]) -> None:
    global _zone_cache
    if not zones:
        _zone_cache = [("NONE", "Keine Zonen geladen", "")]
        return
    items: list[tuple[str, str, str]] = []
    seen_ids: set[str] = set()
    for z in zones:
        name = z.get("legend_text") or ""
        if not name:
            continue
        theme_code = z.get("theme_code") or ""
        theme_text = z.get("theme_text") or ""
        is_nutzung = "nutzungsplanung" in theme_code.lower()
        # Eindeutige ID: Name + Theme (gleicher Zonenname kann in mehreren Themes vorkommen)
        uid = f"{theme_code}::{name}"
        if uid in seen_ids:
            continue
        seen_ids.add(uid)
        area = z.get("area_share")
        pct = z.get("part_in_percent")
        # Label: bei Nicht-Nutzungsplanung Theme-Name voranstellen
        display = name if is_nutzung else f"{name}  [{theme_text or theme_code}]"
        tooltip_parts = []
        if theme_text:
            tooltip_parts.append(theme_text)
        if area is not None:
            tooltip_parts.append(f"{area} m²")
        if pct is not None:
            tooltip_parts.append(f"{pct:.1f}%")
        tooltip = "  ·  ".join(tooltip_parts)
        items.append((uid, display, tooltip))
    _zone_cache = items if items else [("NONE", "Keine Zonen geladen", "")]


def _zone_enum_items(self, context) -> list[tuple[str, str, str]]:
    return _zone_cache


ENVELOPE_SIZES = {0: 0, 1: 32, 2: 48, 3: 48, 4: 64}
PREFERRED_LAYER_NAMES = ("resf", "dprsf", "resfproj", "dprsfproj")
SPINNER_FRAMES = ("|", "/", "-", "\\")
OEREB_NS = {
    "extract": "http://schemas.geo.admin.ch/V_D/OeREB/2.0/Extract",
    "data": "http://schemas.geo.admin.ch/V_D/OeREB/2.0/ExtractData",
}
OEREB_SERVICE_ENDPOINTS = {
    "AG": "https://api.geo.ag.ch/v2/oereb",
    "AI": "https://oereb.ai.ch/ktai/wsgi/oereb",
    "AR": "https://oereb.ar.ch/ktar/wsgi/oereb",
    "BE": "https://www.oereb2.apps.be.ch",
    "BL": "https://oereb.geo.bl.ch",
    "BS": "https://api.oereb.bs.ch",
    "FR": "https://maps.fr.ch/RDPPF_ws/RdppfSVC.svc",
    "GE": "https://ge.ch/terecadastrews/RdppfSVC.svc",
    "GL": "https://map.geo.gl.ch/oereb",
    "GR": "https://oereb.geo.gr.ch/oereb",
    "JU": "https://geo.jura.ch/crdppf_server",
    "LU": "https://svc.geo.lu.ch/oereb",
    "NE": "https://oereb.gis-daten.ch/oereb",
    "SG": "https://oereb.geo.sg.ch/ktsg/wsgi/oereb",
    "SH": "https://oereb.geo.sh.ch",
    "SO": "https://geo.so.ch/api/oereb",
    "SZ": "https://map.geo.sz.ch/oereb",
    "TG": "https://map.geo.tg.ch/services/oereb",
    "TI": "https://crdpp.geo.ti.ch/oereb2",
    "UR": "https://prozessor-oereb.ur.ch/oereb",
    "VD": "https://www.rdppf.vd.ch/ws/RdppfSVC.svc",
    "VS": "https://rdppf.apps.vs.ch",
    "ZG": "https://oereb.zg.ch/ors",
    "ZH": "https://maps.zh.ch/oereb/v2",
}
OEREB_REQUEST_TIMEOUT = 20
OEREB_MAX_WORKERS = 8
GEOSCENE_CRS_KEY = "SRID"
GEOSCENE_CRSX_KEY = "crs x"
GEOSCENE_CRSY_KEY = "crs y"
GEOSCENE_LAT_KEY = "latitude"
GEOSCENE_LON_KEY = "longitude"
GEOSCENE_SCALE_KEY = "scale"
IFC_VENDOR_CACHE_DIR = Path(__file__).resolve().parent / "_vendor"
IFC_VENDOR_WHEELS_DIR = Path(__file__).resolve().parent / "parcel_workflow_vendor" / "wheels"
CANTON_ITEMS = (
    ("AG", "AG", "Aargau"),
    ("AI", "AI", "Appenzell Innerrhoden"),
    ("AR", "AR", "Appenzell Ausserrhoden"),
    ("BE", "BE", "Bern"),
    ("BL", "BL", "Basel-Landschaft"),
    ("BS", "BS", "Basel-Stadt"),
    ("FL", "FL", "Liechtenstein"),
    ("FR", "FR", "Fribourg"),
    ("GE", "GE", "Geneve"),
    ("GL", "GL", "Glarus"),
    ("GR", "GR", "Graubuenden"),
    ("JU", "JU", "Jura"),
    ("LU", "LU", "Luzern"),
    ("NE", "NE", "Neuchatel"),
    ("NW", "NW", "Nidwalden"),
    ("OW", "OW", "Obwalden"),
    ("SG", "SG", "St. Gallen"),
    ("SH", "SH", "Schaffhausen"),
    ("SO", "SO", "Solothurn"),
    ("SZ", "SZ", "Schwyz"),
    ("TG", "TG", "Thurgau"),
    ("TI", "TI", "Ticino"),
    ("UR", "UR", "Uri"),
    ("VD", "VD", "Vaud"),
    ("VS", "VS", "Valais"),
    ("ZG", "ZG", "Zug"),
    ("ZH", "ZH", "Zuerich"),
)


# Kanton-Kürzel → Vollname wie ihn terrara.ch in der URL erwartet
CANTON_TO_TERRARA: dict[str, str] = {abbr: name.upper() for abbr, _, name in CANTON_ITEMS}


class ParcelAddonError(Exception):
    pass


def candidate_project_roots() -> list[Path]:
    home = Path.home()
    return [
        Path(__file__).resolve().parent.parent,
        home / "building-permit-boundary-check",
        home / "Documents" / "building-permit-boundary-check",
        home / "Desktop" / "building-permit-boundary-check",
        home / "Downloads" / "building-permit-boundary-check",
    ]


def looks_like_project_root(path: Path) -> bool:
    return (
        path.exists()
        and (path / "CodeJonas").is_dir()
        and (path / "Add-On").is_dir()
    )


def resolve_project_root(configured_path: str) -> Path | None:
    if configured_path:
        candidate = Path(bpy.path.abspath(configured_path)).expanduser()
        if looks_like_project_root(candidate):
            return candidate

    for candidate in candidate_project_roots():
        if looks_like_project_root(candidate):
            return candidate
    return None


def extract_wheel_if_needed(wheel_path: Path, target_dir: Path) -> Path:
    marker = target_dir / ".extracted"
    if marker.exists():
        return target_dir
    target_dir.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(wheel_path) as archive:
        archive.extractall(target_dir)
    marker.write_text(wheel_path.name, encoding="utf-8")
    return target_dir


def candidate_ifcopenshell_wheel_dirs() -> list[Path]:
    addon_dir = Path(__file__).resolve().parent
    candidates: list[Path] = [
        IFC_VENDOR_WHEELS_DIR,
        addon_dir / "bonsai" / "wheels",
        addon_dir / "parcel_workflow_vendor" / "wheels",
    ]

    # Blender-Extensions (Bonsai als installierte Extension)
    home = Path.home()
    for blender_base in [
        home / "Library" / "Application Support" / "Blender",
        home / ".config" / "blender",
        Path(os.environ.get("APPDATA", "")) / "Blender Foundation" / "Blender",
    ]:
        if blender_base.exists():
            for version_dir in sorted(blender_base.iterdir(), reverse=True):
                bonsai_wheels = version_dir / "extensions" / "blender_org" / "bonsai" / "wheels"
                if bonsai_wheels.exists():
                    candidates.append(bonsai_wheels)

    for project_root in candidate_project_roots():
        candidates.extend(
            [
                project_root / "Add-On" / "parcel_workflow_vendor" / "wheels",
                project_root / "Add-On" / "bonsai" / "wheels",
            ]
        )

    unique_candidates: list[Path] = []
    seen: set[str] = set()
    for candidate in candidates:
        key = str(candidate)
        if key in seen:
            continue
        seen.add(key)
        unique_candidates.append(candidate)
    return unique_candidates


def ensure_ifcopenshell() -> tuple[Any, Any]:
    try:
        import ifcopenshell  # type: ignore
        import ifcopenshell.geom  # type: ignore
        return ifcopenshell, ifcopenshell.geom
    except Exception:
        pass

    wheel_candidates: list[Path] = []
    for wheels_dir in candidate_ifcopenshell_wheel_dirs():
        wheel_candidates.extend(sorted(wheels_dir.glob("ifcopenshell-*.whl")))
    if not wheel_candidates:
        raise ParcelAddonError("IfcOpenShell-Wheel wurde nicht gefunden.")

    py_tag = f"{sys.version_info.major}{sys.version_info.minor}"
    supported_tags = (f"py{py_tag}", f"cp{py_tag}")
    available_names = [candidate.name for candidate in wheel_candidates]

    for wheel_path in wheel_candidates:
        if not any(tag in wheel_path.name for tag in supported_tags):
            continue
        extract_dir = extract_wheel_if_needed(wheel_path, IFC_VENDOR_CACHE_DIR / wheel_path.stem)
        extract_dir_str = str(extract_dir)
        if extract_dir_str not in sys.path:
            sys.path.insert(0, extract_dir_str)
        try:
            import ifcopenshell  # type: ignore
            import ifcopenshell.geom  # type: ignore
            return ifcopenshell, ifcopenshell.geom
        except Exception:
            # Cache kann korrupt/halb extrahiert sein → einmal neu extrahieren und nochmals versuchen.
            try:
                shutil.rmtree(extract_dir, ignore_errors=True)
                extract_dir = extract_wheel_if_needed(wheel_path, extract_dir)
                extract_dir_str = str(extract_dir)
                if extract_dir_str not in sys.path:
                    sys.path.insert(0, extract_dir_str)
                import ifcopenshell  # type: ignore
                import ifcopenshell.geom  # type: ignore
                return ifcopenshell, ifcopenshell.geom
            except Exception:
                continue

    raise ParcelAddonError(
        "IfcOpenShell konnte nicht geladen werden. "
        f"Blender-Python erwartet {supported_tags[0]} (oder {supported_tags[1]}), "
        f"gefunden: {', '.join(available_names) if available_names else 'keine'}."
    )


def resolve_docker_executable() -> str | None:
    candidates = [
        shutil.which("docker"),
        "/usr/local/bin/docker",
        "/opt/homebrew/bin/docker",
        "/Applications/Docker.app/Contents/Resources/bin/docker",
    ]
    for candidate in candidates:
        if candidate and Path(candidate).exists():
            return str(candidate)
    return None


def docker_process_env() -> dict[str, str]:
    env = os.environ.copy()
    path_entries = env.get("PATH", "").split(os.pathsep) if env.get("PATH") else []
    extra_entries = [
        "/usr/local/bin",
        "/opt/homebrew/bin",
        "/Applications/Docker.app/Contents/Resources/bin",
        "/usr/bin",
        "/bin",
        "/usr/sbin",
        "/sbin",
    ]
    merged_entries = []
    for entry in [*path_entries, *extra_entries]:
        if entry and entry not in merged_entries:
            merged_entries.append(entry)
    env["PATH"] = os.pathsep.join(merged_entries)
    env.setdefault("HOME", str(Path.home()))
    return env


def map_container_data_path_to_host(path_value: str, project_root: Path) -> str:
    container_prefix = "/app/data"
    if not path_value.startswith(container_prefix):
        return path_value
    relative_part = path_value[len(container_prefix):].lstrip("/")
    return str((project_root / "CodeJonas" / "data" / relative_part).resolve())


def load_oereb_json(oereb_json_path: Path, props: Any) -> bool:
    try:
        data = json.loads(oereb_json_path.read_text(encoding="utf-8"))
    except Exception:
        return False
    zones = data.get("zones") or []
    if not zones:
        return False
    update_zone_cache(zones)
    primary = data.get("primary_zone") or zones[0].get("legend_text") or ""
    props.last_oereb_zone = primary
    municipality = data.get("municipality") or ""
    props.last_oereb_municipality = municipality
    if municipality and not props.gemeinde:
        props.gemeinde = municipality
    if primary in [item[0] for item in _zone_cache]:
        props.selected_zone = primary
    return True


def _oereb_first_text(element: ET.Element | None, xpath: str) -> str | None:
    if element is None:
        return None
    node = element.find(xpath, OEREB_NS)
    if node is None or node.text is None:
        return None
    text = node.text.strip()
    return text or None


def _oereb_localized_text(element: ET.Element | None, xpath: str) -> str | None:
    return _oereb_first_text(element, xpath)


def _oereb_to_int(value: str | None) -> int | None:
    if value is None:
        return None
    try:
        return int(value)
    except ValueError:
        return None


def _oereb_to_float(value: str | None) -> float | None:
    if value is None:
        return None
    try:
        return float(value)
    except ValueError:
        return None


def build_oereb_extract_url(base_url: str, egrid: str) -> str:
    return f"{base_url.rstrip('/')}/extract/xml/?{urllib.parse.urlencode({'EGRID': egrid})}"


def fetch_oereb_extract_xml(base_url: str, egrid: str) -> tuple[str, str]:
    url = build_oereb_extract_url(base_url, egrid)
    request = urllib.request.Request(
        url,
        headers={
            "Accept": "application/xml,text/xml;q=0.9,*/*;q=0.1",
            "User-Agent": "ParcelWorkflowBlenderAddon/1.0",
        },
    )
    with urllib.request.urlopen(request, timeout=OEREB_REQUEST_TIMEOUT) as response:
        payload = response.read()
    text = payload.decode("utf-8", errors="replace")
    if "GetExtractByIdResponse" not in text:
        raise ParcelAddonError("Antwort ist kein OEREB-XML-Extract.")
    return url, text


def _try_fetch_oereb_endpoint(canton: str, base_url: str, egrid: str) -> dict[str, str] | None:
    try:
        extract_url, xml_text = fetch_oereb_extract_xml(base_url, egrid)
    except (ParcelAddonError, urllib.error.URLError, TimeoutError, ValueError):
        return None
    return {
        "resolved_canton": canton,
        "service_url": base_url,
        "extract_url": extract_url,
        "xml_text": xml_text,
    }


def fetch_oereb_extract_for_switzerland(egrid: str, preferred_canton: str | None = None) -> dict[str, str]:
    preferred = (preferred_canton or "").upper()
    selected_items: list[tuple[str, str]]
    if preferred in OEREB_SERVICE_ENDPOINTS:
        selected_items = [(preferred, OEREB_SERVICE_ENDPOINTS[preferred])]
        remaining = [(code, url) for code, url in OEREB_SERVICE_ENDPOINTS.items() if code != preferred]
    else:
        selected_items = []
        remaining = list(OEREB_SERVICE_ENDPOINTS.items())

    for canton, base_url in selected_items:
        result = _try_fetch_oereb_endpoint(canton, base_url, egrid)
        if result is not None:
            return result

    with ThreadPoolExecutor(max_workers=min(OEREB_MAX_WORKERS, len(remaining) or 1)) as executor:
        futures = {
            executor.submit(_try_fetch_oereb_endpoint, canton, base_url, egrid): canton
            for canton, base_url in remaining
        }
        for future in as_completed(futures):
            result = future.result()
            if result is not None:
                return result

    raise ParcelAddonError(f"Kein OEREB-Extract fuer {egrid} in den konfigurierten Schweizer Diensten gefunden.")


def parse_oereb_real_estate(root: ET.Element) -> dict[str, Any]:
    real_estate = root.find(".//data:RealEstate", OEREB_NS)
    if real_estate is None:
        return {}
    return {
        "egrid": _oereb_first_text(real_estate, "data:EGRID"),
        "number": _oereb_first_text(real_estate, "data:Number"),
        "ident_nd": _oereb_first_text(real_estate, "data:IdentDN"),
        "municipality": _oereb_localized_text(real_estate, "data:Municipality/data:Name/data:LocalisedText/data:Text"),
        "subunit_of_land_register": _oereb_localized_text(real_estate, "data:SubunitOfLandRegister/data:LocalisedText/data:Text"),
        "land_registry_area": _oereb_to_int(_oereb_first_text(real_estate, "data:LandRegistryArea")),
    }


def parse_oereb_payload(xml_text: str, egrid: str, resolved_canton: str, service_url: str, extract_url: str) -> dict[str, Any]:
    root = ET.fromstring(xml_text)
    restrictions = root.findall(".//data:RestrictionOnLandownership", OEREB_NS)

    # Accumulate area_share per unique (theme_code, legend_text, law_status, symbol_ref)
    # so that zones covering multiple sub-polygons are correctly ranked by total area.
    aggregated: dict[tuple[str, str, str | None, str | None], dict[str, Any]] = {}

    for restriction in restrictions:
        entry = {
            "theme_code": _oereb_first_text(restriction, "data:Theme/data:Code") or "",
            "theme_text": _oereb_localized_text(restriction, "data:Theme/data:Text/data:LocalisedText/data:Text") or "",
            "legend_text": _oereb_localized_text(restriction, "data:LegendText/data:LocalisedText/data:Text") or "",
            "type_code": _oereb_first_text(restriction, "data:TypeCode"),
            "symbol_ref": _oereb_first_text(restriction, "data:SymbolRef"),
            "law_status": _oereb_first_text(restriction, "data:Lawstatus/data:Code"),
            "area_share": _oereb_to_int(_oereb_first_text(restriction, "data:AreaShare")),
            "part_in_percent": _oereb_to_float(_oereb_first_text(restriction, "data:PartInPercent")),
        }
        if not entry["legend_text"]:
            continue
        key = (entry["theme_code"], entry["legend_text"], entry["law_status"], entry["symbol_ref"])
        if key in aggregated:
            existing = aggregated[key]
            if entry["area_share"] is not None:
                existing["area_share"] = (existing["area_share"] or 0) + entry["area_share"]
            if entry["part_in_percent"] is not None:
                existing["part_in_percent"] = (existing["part_in_percent"] or 0.0) + entry["part_in_percent"]
        else:
            aggregated[key] = entry

    legend_entries = list(aggregated.values())

    # Nur Zonen die die Parzelle tatsächlich berühren (area_share > 0 oder part_in_percent > 0).
    # Einträge ohne Flächenangabe sind Legendeneinträge der Gemeinde, nicht der Parzelle.
    def _has_area(z: dict) -> bool:
        return (z.get("area_share") or 0) > 0 or (z.get("part_in_percent") or 0.0) > 0.0

    def _sort_key(z: dict) -> tuple:
        is_nutzung = "nutzungsplanung" in (z.get("theme_code") or "").lower()
        return (not is_nutzung, -(z.get("area_share") or 0), -(z.get("part_in_percent") or 0.0))

    zones = sorted([e for e in legend_entries if _has_area(e)], key=_sort_key)

    primary_zone = zones[0]["legend_text"] if zones else None

    return {
        "requested_egrid": egrid,
        "resolved_canton": resolved_canton,
        "service_url": service_url,
        "extract_url": extract_url,
        "real_estate": parse_oereb_real_estate(root),
        "legend_entries": legend_entries,
        "zones": zones,
        "primary_zone": primary_zone,
    }


def fetch_oereb_payload(egrid: str, preferred_canton: str | None = None) -> dict[str, Any]:
    extracted = fetch_oereb_extract_for_switzerland(egrid, preferred_canton=preferred_canton)
    return parse_oereb_payload(
        extracted["xml_text"],
        egrid=egrid,
        resolved_canton=extracted["resolved_canton"],
        service_url=extracted["service_url"],
        extract_url=extracted["extract_url"],
    )


def redraw_ui() -> None:
    for window in bpy.context.window_manager.windows:
        for area in window.screen.areas:
            area.tag_redraw()


def sanitize_attribute_value(value: Any) -> Any | None:
    if value is None:
        return None
    if isinstance(value, (bool, int, float, str)):
        return value
    return json.dumps(value, ensure_ascii=False)


def ensure_scene_idprop_metadata(scene: bpy.types.Scene, key: str, description: str, default: Any) -> None:
    rna_ui = scene.get("_RNA_UI")
    if rna_ui is None:
        scene["_RNA_UI"] = {}
        rna_ui = scene["_RNA_UI"]
    if key not in rna_ui:
        rna_ui[key] = {"description": description, "default": default}


def apply_geoscene_reference(scene: bpy.types.Scene, origin: tuple[float, float, float], crs: str = "EPSG:2056") -> None:
    ensure_scene_idprop_metadata(scene, GEOSCENE_CRS_KEY, "Map Coordinate Reference System", "")
    ensure_scene_idprop_metadata(scene, GEOSCENE_CRSX_KEY, "Scene x origin in CRS space", 0.0)
    ensure_scene_idprop_metadata(scene, GEOSCENE_CRSY_KEY, "Scene y origin in CRS space", 0.0)
    ensure_scene_idprop_metadata(scene, GEOSCENE_SCALE_KEY, "Map scale denominator", 1.0)

    scene[GEOSCENE_CRS_KEY] = crs
    scene[GEOSCENE_CRSX_KEY] = float(origin[0])
    scene[GEOSCENE_CRSY_KEY] = float(origin[1])
    scene[GEOSCENE_SCALE_KEY] = 1.0

    if Transformer is not None:
        try:
            transformer = Transformer.from_crs(crs, "EPSG:4326", always_xy=True)
            lon, lat = transformer.transform(float(origin[0]), float(origin[1]))
            ensure_scene_idprop_metadata(scene, GEOSCENE_LAT_KEY, "Scene origin latitude", 0.0)
            ensure_scene_idprop_metadata(scene, GEOSCENE_LON_KEY, "Scene origin longitude", 0.0)
            scene[GEOSCENE_LAT_KEY] = float(lat)
            scene[GEOSCENE_LON_KEY] = float(lon)
        except Exception:
            pass


def wgs84_to_scene_crs(lon: float, lat: float) -> tuple[float, float]:
    scene_crs = bpy.context.scene.get(GEOSCENE_CRS_KEY, "EPSG:2056")
    if Transformer is None:
        raise ParcelAddonError("pyproj ist nicht verfuegbar, um die GeoScene-Koordinaten zu berechnen.")
    transformer = Transformer.from_crs("EPSG:4326", scene_crs, always_xy=True)
    x, y = transformer.transform(lon, lat)
    return float(x), float(y)


def _iter_geometry_coords(geometry: dict[str, Any]):
    coordinates = geometry.get("coordinates")
    if coordinates is None:
        return

    def walk(value):
        if not isinstance(value, list):
            return
        if value and isinstance(value[0], (int, float)):
            yield value
            return
        for child in value:
            yield from walk(child)

    yield from walk(coordinates)


def hadr_origin(features: list[dict[str, Any]]) -> tuple[float, float, float] | None:
    for feature in features:
        if not isinstance(feature, dict):
            continue
        properties = feature.get("properties") or {}
        geometry = feature.get("geometry")
        if not isinstance(properties, dict) or not isinstance(geometry, dict):
            continue
        if str(properties.get("source_layer") or "").lower() != "hadr":
            continue
        if geometry.get("type") != "Point":
            continue
        coordinates = geometry.get("coordinates")
        if not isinstance(coordinates, list) or len(coordinates) < 2:
            continue
        if len(coordinates) >= 3:
            return float(coordinates[0]), float(coordinates[1]), float(coordinates[2])
        return float(coordinates[0]), float(coordinates[1]), 0.0
    return None


def determine_local_origin(features: list[dict[str, Any]]) -> tuple[float, float, float]:
    preferred_hadr_origin = hadr_origin(features)
    if preferred_hadr_origin is not None:
        return preferred_hadr_origin

    min_x = min_y = float("inf")
    max_x = max_y = float("-inf")
    has_coord = False

    for feature in features:
        if not isinstance(feature, dict):
            continue
        geometry = feature.get("geometry")
        if not isinstance(geometry, dict):
            continue
        for coord in _iter_geometry_coords(geometry):
            if len(coord) < 2:
                continue
            x = float(coord[0])
            y = float(coord[1])
            min_x = min(min_x, x)
            min_y = min(min_y, y)
            max_x = max(max_x, x)
            max_y = max(max_y, y)
            has_coord = True

    if not has_coord:
        return 0.0, 0.0, 0.0

    return (min_x + max_x) * 0.5, (min_y + max_y) * 0.5, 0.0


def create_collection(name: str, parent: bpy.types.Collection) -> bpy.types.Collection:
    existing = bpy.data.collections.get(name)
    if existing is not None:
        if parent.children.get(existing.name) is None:
            parent.children.link(existing)
        return existing
    collection = bpy.data.collections.new(name)
    parent.children.link(collection)
    return collection


def clear_collection_hierarchy(collection: bpy.types.Collection) -> None:
    for child in list(collection.children):
        clear_collection_hierarchy(child)
        bpy.data.collections.remove(child)
    clear_collection_objects(collection)


def clear_collection_objects(collection: bpy.types.Collection) -> None:
    for obj in list(collection.objects):
        bpy.data.objects.remove(obj, do_unlink=True)


def apply_properties(obj: bpy.types.Object, properties: dict[str, Any], source_name: str) -> None:
    obj["source_name"] = source_name
    obj["crs_hint"] = "EPSG:2056"
    for key, value in properties.items():
        clean = sanitize_attribute_value(value)
        if clean is not None:
            obj[key] = clean


def object_name(base_name: str, properties: dict[str, Any], index: int) -> str:
    egrid = properties.get("EGRIS_EGRID") or properties.get("EGRID") or properties.get("egrid")
    number = properties.get("Nummer") or properties.get("nummer")
    is_target = properties.get("is_target_parcel")
    suffix = []
    if is_target:
        suffix.append("target")
    if egrid:
        suffix.append(str(egrid))
    elif number:
        suffix.append(str(number))
    suffix.append(f"{index:04d}")
    return "_".join([base_name, *suffix])


def _read_uint(data: bytes, offset: int, endian: str) -> tuple[int, int]:
    return struct.unpack_from(f"{endian}I", data, offset)[0], offset + 4


def _read_double(data: bytes, offset: int, endian: str) -> tuple[float, int]:
    return struct.unpack_from(f"{endian}d", data, offset)[0], offset + 8


def parse_gpkg_geometry(blob: bytes) -> dict[str, Any] | None:
    if not blob:
        return None
    if blob[:2] != b"GP":
        raise ParcelAddonError("Ungueltiger GeoPackage-Header.")
    flags = blob[3]
    envelope_indicator = (flags >> 1) & 0b111
    wkb_offset = 8 + ENVELOPE_SIZES.get(envelope_indicator, 0)
    return parse_wkb(blob[wkb_offset:])[0]


def parse_wkb(data: bytes, offset: int = 0) -> tuple[dict[str, Any], int]:
    start = offset
    byte_order = data[offset]
    endian = "<" if byte_order == 1 else ">"
    offset += 1
    raw_type, offset = _read_uint(data, offset, endian)
    has_z = bool(raw_type & 0x80000000)
    geometry_type = raw_type & 0xFF
    dims = 3 if has_z else 2

    def read_point() -> tuple[list[float], int]:
        x, next_offset = _read_double(data, offset, endian)
        y, next_offset = _read_double(data, next_offset, endian)
        if dims == 3:
            z, next_offset = _read_double(data, next_offset, endian)
            return [x, y, z], next_offset
        return [x, y], next_offset

    if geometry_type == 1:
        point, offset = read_point()
        return {"type": "Point", "coordinates": point}, offset - start

    if geometry_type == 2:
        count, offset = _read_uint(data, offset, endian)
        coords = []
        for _ in range(count):
            point, offset = read_point()
            coords.append(point)
        return {"type": "LineString", "coordinates": coords}, offset - start

    if geometry_type == 3:
        ring_count, offset = _read_uint(data, offset, endian)
        rings = []
        for _ in range(ring_count):
            point_count, offset = _read_uint(data, offset, endian)
            ring = []
            for _ in range(point_count):
                point, offset = read_point()
                ring.append(point)
            rings.append(ring)
        return {"type": "Polygon", "coordinates": rings}, offset - start

    if geometry_type == 4:
        child_count, offset = _read_uint(data, offset, endian)
        coords = []
        for _ in range(child_count):
            child, child_size = parse_wkb(data, offset)
            offset += child_size
            coords.append(child["coordinates"])
        return {"type": "MultiPoint", "coordinates": coords}, offset - start

    if geometry_type == 5:
        child_count, offset = _read_uint(data, offset, endian)
        coords = []
        for _ in range(child_count):
            child, child_size = parse_wkb(data, offset)
            offset += child_size
            coords.append(child["coordinates"])
        return {"type": "MultiLineString", "coordinates": coords}, offset - start

    if geometry_type == 6:
        child_count, offset = _read_uint(data, offset, endian)
        coords = []
        for _ in range(child_count):
            child, child_size = parse_wkb(data, offset)
            offset += child_size
            coords.append(child["coordinates"])
        return {"type": "MultiPolygon", "coordinates": coords}, offset - start

    raise ParcelAddonError(f"Nicht unterstuetzter Geometrietyp: {geometry_type}")


def feature_tables(connection: sqlite3.Connection) -> list[tuple[str, str]]:
    rows = connection.execute(
        """
        SELECT c.table_name, g.column_name
        FROM gpkg_contents AS c
        JOIN gpkg_geometry_columns AS g ON c.table_name = g.table_name
        WHERE c.data_type = 'features'
        ORDER BY c.table_name
        """
    ).fetchall()
    return [(str(table_name), str(column_name)) for table_name, column_name in rows]


def choose_layer(tables: list[tuple[str, str]]) -> tuple[str, str]:
    for table_name, geometry_column in tables:
        if table_name.lower() in PREFERRED_LAYER_NAMES:
            return table_name, geometry_column
    for table_name, geometry_column in tables:
        if "resf" in table_name.lower():
            return table_name, geometry_column
    return tables[0]


def choose_layers(
    tables: list[tuple[str, str]],
    include_resf: bool = True,
    include_hadr: bool = True,
) -> list[tuple[str, str]]:
    selected: list[tuple[str, str]] = []
    lowered_lookup = {table_name.lower(): (table_name, geometry_column) for table_name, geometry_column in tables}

    if include_resf:
        for layer_name in PREFERRED_LAYER_NAMES:
            if layer_name in lowered_lookup:
                selected.append(lowered_lookup[layer_name])
                break
        else:
            for table_name, geometry_column in tables:
                if "resf" in table_name.lower():
                    selected.append((table_name, geometry_column))
                    break

    if include_hadr and "hadr" in lowered_lookup:
        hadr_layer = lowered_lookup["hadr"]
        if hadr_layer not in selected:
            selected.append(hadr_layer)

    if not selected and tables:
        selected.append(tables[0])

    return selected


def gpkg_to_geojson(input_path: Path, output_path: Path, only_resf: bool = True, include_hadr: bool = True) -> tuple[int, list[str]]:
    with sqlite3.connect(input_path) as connection:
        tables = feature_tables(connection)
        if not tables:
            raise ParcelAddonError("Keine Feature-Layer im GeoPackage gefunden.")

        features = []
        layer_names: list[str] = []
        selected_layers = choose_layers(tables, include_resf=only_resf, include_hadr=include_hadr) if only_resf or include_hadr else [tables[0]]

        for table_name, geometry_column in selected_layers:
            layer_names.append(table_name)
            cursor = connection.execute(f'SELECT * FROM "{table_name}" WHERE "{geometry_column}" IS NOT NULL')
            rows = cursor.fetchall()
            columns = [description[0] for description in cursor.description]

            for row in rows:
                row_data = dict(zip(columns, row))
                blob = row_data.pop(geometry_column, None)
                geometry = parse_gpkg_geometry(blob)
                if geometry is None:
                    continue
                row_data.setdefault("source_layer", table_name)
                features.append(
                    {
                        "type": "Feature",
                        "properties": row_data,
                        "geometry": geometry,
                    }
                )

    if not features:
        raise ParcelAddonError("Keine Geometrien im gewaehlten Layer gefunden.")

    payload = {"type": "FeatureCollection", "features": features}
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, ensure_ascii=False), encoding="utf-8")
    return len(features), layer_names


def append_oereb_to_geojson(geojson_path: Path, zones: list[dict], egrid: str, municipality: str = "") -> None:
    """Speichert OEREB-Zonen als Metadaten im GeoJSON (kein Feature → keine Blender-Objekte)."""
    payload = json.loads(geojson_path.read_text(encoding="utf-8"))
    payload["oereb"] = {
        "egrid": egrid,
        "municipality": municipality,
        "primary_zone": zones[0].get("legend_text") if zones else None,
        "zones": zones,
    }
    geojson_path.write_text(json.dumps(payload, ensure_ascii=False), encoding="utf-8")


def zones_from_geojson(geojson_path: Path) -> list[dict]:
    """Liest OEREB-Zonen aus den GeoJSON-Metadaten, nur mit Flächenanteil > 0."""
    try:
        payload = json.loads(geojson_path.read_text(encoding="utf-8"))
    except Exception:
        return []
    zones = (payload.get("oereb") or {}).get("zones") or []
    return [z for z in zones if (z.get("area_share") or 0) > 0 or (z.get("part_in_percent") or 0.0) > 0.0]


def _municipality_from_lv95_coords(e: float, n: float) -> str:
    """Räumliche Abfrage via GeoAdmin MapServer Identify.
    Gibt LV95-Punkt (E, N) → offizieller Gemeindename aus SwissBOUNDARIES3D zurück.
    API: https://api3.geo.admin.ch/rest/services/ech/MapServer/identify
    Layer: ch.swisstopo.swissboundaries3d-gemeinde-flaeche.fill"""
    try:
        margin = 500
        params = urllib.parse.urlencode({
            "geometry":     f"{e:.1f},{n:.1f}",
            "geometryType": "esriGeometryPoint",
            "layers":       "all:ch.swisstopo.swissboundaries3d-gemeinde-flaeche.fill",
            "mapExtent":    f"{e-margin:.1f},{n-margin:.1f},{e+margin:.1f},{n+margin:.1f}",
            "imageDisplay": "100,100,96",
            "tolerance":    "0",
            "returnGeometry": "false",
            "sr":           "2056",
        })
        url = f"https://api3.geo.admin.ch/rest/services/ech/MapServer/identify?{params}"
        req = urllib.request.Request(
            url,
            headers={"User-Agent": "Blender-ParcelWorkflow/1.0", "Accept": "application/json"},
        )
        with urllib.request.urlopen(req, timeout=12) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        results = data.get("results") or []
        if results:
            # SwissBOUNDARIES3D enthält historische UND aktuelle Einträge (is_current_jahr).
            # Märwil ist z.B. eine historische Gemeinde, Affeltrangen die aktuelle (Fusion).
            # → Zuerst nach is_current_jahr=True filtern, sonst höchstes Jahr nehmen.
            def _get_name(attrs):
                return (attrs.get("gemname") or attrs.get("gemndname")
                        or attrs.get("GEMNAME") or attrs.get("GEMNDNAME")
                        or attrs.get("name") or attrs.get("NAME") or "")

            current = [r for r in results
                       if r.get("attributes", {}).get("is_current_jahr")]
            if current:
                name = _get_name(current[0].get("attributes") or {})
            else:
                # Kein is_current_jahr-Feld → Eintrag mit höchstem Jahr wählen
                best = max(results,
                           key=lambda r: r.get("attributes", {}).get("jahr", 0))
                name = _get_name(best.get("attributes") or {})
            if name:
                return str(name).strip()
    except Exception as exc:
        print(f"  Gemeinde-Identify fehlgeschlagen ({e:.0f}/{n:.0f}): {exc}")
    return ""


def address_from_geojson(geojson_path: Path) -> str:
    """Liest Strassenname, Hausnummer, PLZ, Ortschaftsname aus dem HADR-Feature.

    Beispiel-Ergebnis: "Kantonsstrasse 19, 8862 Schübelbach"
    """
    try:
        payload = json.loads(geojson_path.read_text(encoding="utf-8"))
    except Exception:
        return ""
    for feature in payload.get("features") or []:
        props = feature.get("properties") or {}
        if str(props.get("source_layer") or "").lower() != "hadr":
            continue
        strasse = str(props.get("Strassenname") or "").strip()
        hausnr  = str(props.get("Hausnummer")   or "").strip()
        plz     = str(props.get("PLZ")           or "").strip()
        ort     = str(props.get("Ortschaftsname") or "").strip()
        street_part = (f"{strasse} {hausnr}".strip()) if strasse else ""
        city_part   = (f"{plz} {ort}".strip())        if (plz or ort) else ""
        parts = [p for p in (street_part, city_part) if p]
        if parts:
            return ", ".join(parts)
    return ""


def municipality_from_geojson(geojson_path: Path) -> str:
    """Gibt den offiziellen Gemeindenamen zurück.

    Priorität:
    1) OEREB-Metadaten (schon aufgelöst)
    2) Direkte Gemeindenamen-Felder im GeoJSON
    3) Räumliche Identify-Abfrage mit dem Parzellenzentroid auf SwissBOUNDARIES3D
       → liefert immer den politischen Gemeindenamen, nicht den Ortsteilnamen
    4) BFSNr → MapServer find (Fallback)
    5) Ortschaftsname (letzter Ausweg – ist oft ein Ortsteil, z.B. «Märwil» ≠ «Affeltangen»)
    """
    try:
        payload = json.loads(geojson_path.read_text(encoding="utf-8"))
    except Exception:
        return ""

    features = payload.get("features") or []

    # 1) OEREB-Metadaten
    oereb_muni = (payload.get("oereb") or {}).get("municipality") or ""
    if oereb_muni:
        return oereb_muni

    # 2) Direkte Gemeindenamen-Felder
    for feature in features:
        props = feature.get("properties") or {}
        for field in ("Gemeindename", "GEMEINDENAME", "gemndname", "GDE_NAME", "municipality"):
            name = str(props.get(field) or "").strip()
            if name:
                return name

    # 3) Räumliche Abfrage: Parzellenzentroid → SwissBOUNDARIES3D identify
    #    Zielparzelle bevorzugen (is_target_parcel=True), dann alle anderen Features
    target = next(
        (f for f in features
         if (f.get("properties") or {}).get("is_target_parcel") in (True, 1, "1", "true", "True")),
        None,
    )
    ordered = ([target] if target else []) + [f for f in features if f is not target]
    for feat in ordered:
        if not feat:
            continue
        geom   = feat.get("geometry") or {}
        coords = geom.get("coordinates")
        if not coords:
            continue
        try:
            if geom["type"] == "Polygon":
                ring = coords[0]
            elif geom["type"] == "MultiPolygon":
                ring = coords[0][0]
            else:
                continue
            e = sum(p[0] for p in ring) / len(ring)
            n = sum(p[1] for p in ring) / len(ring)
            if e > 2_400_000 and n > 1_000_000:   # plausible LV95-Bereich
                name = _municipality_from_lv95_coords(e, n)
                if name:
                    return name
        except Exception:
            continue
        break  # nach erstem Polygon-Feature aufhören

    # 4) BFSNr → MapServer find (Fallback)
    for feature in features:
        props = feature.get("properties") or {}
        for field in ("BFSNr", "bfsnr", "BFSNR", "gemndnr"):
            bfsnr = str(props.get(field) or "").strip()
            if bfsnr:
                try:
                    params = urllib.parse.urlencode({
                        "layer":       "ch.swisstopo.swissboundaries3d-gemeinde-flaeche.fill",
                        "searchText":  bfsnr,
                        "searchField": "gemndnr",
                        "returnGeometry": "false",
                    })
                    url = f"https://api3.geo.admin.ch/rest/services/ech/MapServer/find?{params}"
                    req = urllib.request.Request(url, headers={"User-Agent": "Blender-ParcelWorkflow/1.0", "Accept": "application/json"})
                    with urllib.request.urlopen(req, timeout=10) as resp:
                        data = json.loads(resp.read().decode("utf-8"))
                    results = data.get("results") or []
                    if results:
                        attrs = results[0].get("attributes") or {}
                        name = str(attrs.get("gemndname") or attrs.get("name") or "").strip()
                        if name:
                            return name
                except Exception:
                    pass

    # 5) Ortschaftsname – letzter Fallback (kann Ortsteil sein!)
    for feature in features:
        props = feature.get("properties") or {}
        name = str(props.get("Ortschaftsname") or props.get("Name") or "").strip()
        if name:
            return name

    return ""


def xyz_from_coord(coord: list[float], origin: tuple[float, float, float] = (0.0, 0.0, 0.0)) -> tuple[float, float, float]:
    if len(coord) >= 3:
        return float(coord[0]) - origin[0], float(coord[1]) - origin[1], float(coord[2]) - origin[2]
    return float(coord[0]) - origin[0], float(coord[1]) - origin[1], 0.0 - origin[2]


def add_curve_object(name: str, coords_groups: list[tuple[list[tuple[float, float, float]], bool]], collection, properties, source_name):
    curve = bpy.data.curves.new(name, type="CURVE")
    curve.dimensions = "3D"
    for coords, cyclic in coords_groups:
        if len(coords) < 2:
            continue
        spline = curve.splines.new("POLY")
        spline.points.add(len(coords) - 1)
        for index, coord in enumerate(coords):
            spline.points[index].co = (coord[0], coord[1], coord[2], 1.0)
        spline.use_cyclic_u = cyclic
    obj = bpy.data.objects.new(name, curve)
    apply_properties(obj, properties, source_name)
    collection.objects.link(obj)


def add_mesh_polygon_object(name: str, polygon_rings, collection, properties, source_name):
    if not polygon_rings or len(polygon_rings[0]) < 3:
        return
    mesh = bpy.data.meshes.new(name)
    obj = bpy.data.objects.new(name, mesh)
    collection.objects.link(obj)
    apply_properties(obj, properties, source_name)
    bm = bmesh.new()
    try:
        for ring in polygon_rings:
            if len(ring) < 3:
                continue
            coords = ring[:-1] if len(ring) > 2 and ring[0] == ring[-1] else ring
            verts = [bm.verts.new(coord) for coord in coords]
            bm.verts.ensure_lookup_table()
            try:
                bm.faces.new(verts)
            except ValueError:
                pass
        bm.to_mesh(mesh)
        mesh.update()
    finally:
        bm.free()


def add_point_object(name: str, coord, collection, properties, source_name):
    mesh = bpy.data.meshes.new(name)
    mesh.from_pydata([coord], [], [])
    mesh.update()
    obj = bpy.data.objects.new(name, mesh)
    apply_properties(obj, properties, source_name)
    collection.objects.link(obj)


def import_geometry(
    geometry: dict[str, Any],
    properties: dict[str, Any],
    base_name: str,
    collection,
    index: int,
    origin: tuple[float, float, float],
) -> int:
    geometry_type = geometry.get("type")
    coordinates = geometry.get("coordinates")
    if not geometry_type:
        return 0
    name = object_name(base_name, properties, index)

    if geometry_type == "Point":
        add_point_object(name, xyz_from_coord(coordinates, origin), collection, properties, geometry_type)
        return 1
    if geometry_type == "LineString":
        add_curve_object(name, [([xyz_from_coord(coord, origin) for coord in coordinates], False)], collection, properties, geometry_type)
        return 1
    if geometry_type == "Polygon":
        add_mesh_polygon_object(name, [[xyz_from_coord(coord, origin) for coord in ring] for ring in coordinates], collection, properties, geometry_type)
        return 1
    if geometry_type == "MultiLineString":
        add_curve_object(name, [([xyz_from_coord(coord, origin) for coord in line], False) for line in coordinates], collection, properties, geometry_type)
        return 1
    if geometry_type == "MultiPolygon":
        count = 0
        for polygon in coordinates:
            add_mesh_polygon_object(
                f"{name}_{count:04d}",
                [[xyz_from_coord(coord, origin) for coord in ring] for ring in polygon],
                collection,
                properties,
                geometry_type,
            )
            count += 1
        return count
    if geometry_type == "MultiPoint":
        count = 0
        for child_index, coord in enumerate(coordinates):
            add_point_object(f"{name}_{child_index:04d}", xyz_from_coord(coord, origin), collection, properties, geometry_type)
            count += 1
        return count
    return 0


def import_geojson(input_path: Path) -> tuple[int, str]:
    payload = json.loads(input_path.read_text(encoding="utf-8"))
    features = payload.get("features", [])
    if not isinstance(features, list) or not features:
        raise ParcelAddonError("Keine Features im GeoJSON gefunden.")

    root_collection = create_collection(input_path.stem, bpy.context.scene.collection)
    bpy.context.scene["geojson_crs_hint"] = "EPSG:2056"
    local_origin = determine_local_origin(features)
    root_collection["crs_hint"] = "EPSG:2056"
    root_collection["georef_method"] = "GeoScene"
    root_collection["crs x"] = local_origin[0]
    root_collection["crs y"] = local_origin[1]
    root_collection["origin_z"] = local_origin[2]
    apply_geoscene_reference(bpy.context.scene, local_origin, crs="EPSG:2056")
    bpy.context.scene.parcel_workflow.last_origin_e = f"{local_origin[0]:.3f}"
    bpy.context.scene.parcel_workflow.last_origin_n = f"{local_origin[1]:.3f}"
    bpy.context.scene.parcel_workflow.last_origin_z = f"{local_origin[2]:.3f}"
    imported_objects = 0

    for index, feature in enumerate(features):
        if not isinstance(feature, dict):
            continue
        geometry = feature.get("geometry")
        properties = feature.get("properties") or {}
        if geometry is None or not isinstance(properties, dict):
            continue
        layer_name = str(properties.get("source_layer") or input_path.stem)
        layer_collection = create_collection(layer_name, root_collection)
        imported_objects += import_geometry(geometry, properties, input_path.stem, layer_collection, index, local_origin)

    bpy.context.scene.parcel_workflow.last_import_collection = root_collection.name
    return imported_objects, root_collection.name


def scene_project_origin() -> tuple[float, float, float] | None:
    scene = bpy.context.scene
    if GEOSCENE_CRSX_KEY in scene and GEOSCENE_CRSY_KEY in scene:
        return float(scene[GEOSCENE_CRSX_KEY]), float(scene[GEOSCENE_CRSY_KEY]), 0.0
    return None


def ifc_local_placement_offset(placement: Any) -> tuple[float, float, float]:
    if placement is None:
        return 0.0, 0.0, 0.0

    parent_x = parent_y = parent_z = 0.0
    parent = getattr(placement, "PlacementRelTo", None)
    if parent is not None:
        parent_x, parent_y, parent_z = ifc_local_placement_offset(parent)

    relative = getattr(placement, "RelativePlacement", None)
    location = getattr(relative, "Location", None)
    coordinates = getattr(location, "Coordinates", None)
    if coordinates:
        x = float(coordinates[0]) if len(coordinates) > 0 else 0.0
        y = float(coordinates[1]) if len(coordinates) > 1 else 0.0
        z = float(coordinates[2]) if len(coordinates) > 2 else 0.0
    else:
        x = y = z = 0.0
    return parent_x + x, parent_y + y, parent_z + z


def dms_tuple_to_decimal(value: Any) -> float | None:
    if not value:
        return None
    parts = list(value)
    if len(parts) < 3:
        return None
    degrees = float(parts[0])
    minutes = float(parts[1])
    seconds = float(parts[2])
    microseconds = float(parts[3]) if len(parts) > 3 else 0.0
    sign = -1.0 if any(part < 0 for part in parts) else 1.0
    degrees = abs(degrees)
    minutes = abs(minutes)
    seconds = abs(seconds)
    microseconds = abs(microseconds)
    return sign * (degrees + minutes / 60.0 + seconds / 3600.0 + microseconds / 3600000000.0)


def infer_ifc_map_transform(ifc_file: Any) -> dict[str, float] | None:
    conversions = ifc_file.by_type("IfcMapConversion")
    if conversions:
        conversion = conversions[0]
        return {
            "eastings": float(getattr(conversion, "Eastings", 0.0) or 0.0),
            "northings": float(getattr(conversion, "Northings", 0.0) or 0.0),
            "height": float(getattr(conversion, "OrthogonalHeight", 0.0) or 0.0),
            "xaa": float(getattr(conversion, "XAxisAbscissa", 1.0) or 1.0),
            "xao": float(getattr(conversion, "XAxisOrdinate", 0.0) or 0.0),
            "scale": float(getattr(conversion, "Scale", 1.0) or 1.0),
        }

    sites = ifc_file.by_type("IfcSite")
    if not sites:
        return None
    site = sites[0]
    lon = dms_tuple_to_decimal(getattr(site, "RefLongitude", None))
    lat = dms_tuple_to_decimal(getattr(site, "RefLatitude", None))
    if lon is None or lat is None:
        return None

    try:
        site_x, site_y = wgs84_to_scene_crs(lon, lat)
    except Exception:
        return None

    local_x, local_y, local_z = ifc_local_placement_offset(getattr(site, "ObjectPlacement", None))

    ref_elevation = getattr(site, "RefElevation", None)
    elevation = float(ref_elevation) if ref_elevation is not None else local_z
    return {
        "eastings": site_x - local_x,
        "northings": site_y - local_y,
        "height": elevation - local_z,
        "xaa": 1.0,
        "xao": 0.0,
        "scale": 1.0,
    }


def ifc_vertex_to_scene_local(
    x: float,
    y: float,
    z: float,
    scene_origin: tuple[float, float, float] | None,
    ifc_map_transform: dict[str, float] | None,
) -> tuple[float, float, float]:
    if ifc_map_transform is not None:
        theta_cos = ifc_map_transform["xaa"]
        theta_sin = ifc_map_transform["xao"]
        scale = ifc_map_transform["scale"]
        map_x = (scale * theta_cos * x) - (scale * theta_sin * y) + ifc_map_transform["eastings"]
        map_y = (scale * theta_sin * x) + (scale * theta_cos * y) + ifc_map_transform["northings"]
        map_z = (scale * z) + ifc_map_transform["height"]
    else:
        map_x, map_y, map_z = x, y, z
    if scene_origin is None:
        return float(map_x), float(map_y), float(map_z)
    return (
        float(map_x) - scene_origin[0],
        float(map_y) - scene_origin[1],
        float(map_z) - scene_origin[2],
    )


def _safe_ifc_setting(settings: Any, keys: tuple[str, ...], value: Any) -> None:
    for key in keys:
        try:
            settings.set(key, value)
            return
        except Exception:
            continue


def _build_ifc_geom_settings(ifc_geom: Any, fallback: bool = False) -> Any:
    settings = ifc_geom.settings()
    _safe_ifc_setting(settings, ("use-world-coords", "use_world_coords"), True)
    _safe_ifc_setting(settings, ("apply-default-materials", "apply_default_materials"), False)
    if fallback:
        _safe_ifc_setting(settings, ("disable-opening-subtractions", "disable_opening_subtractions"), True)
        _safe_ifc_setting(settings, ("disable-triangulation", "disable_triangulation"), False)
    return settings


def is_ifc_terrain_product(product: Any) -> bool:
    predefined_type = str(getattr(product, "PredefinedType", "") or "").upper()
    if product.is_a("IfcGeographicElement") and predefined_type == "TERRAIN":
        return True

    product_name = str(getattr(product, "Name", "") or "").casefold()
    terrain_terms = ("terrain", "gelände", "gelaende", "freifläche", "freiflaeche")
    return product.is_a("IfcGeographicElement") and any(term in product_name for term in terrain_terms)


def apply_collection_z_offset(collection: bpy.types.Collection, z_offset: float) -> float:
    if abs(z_offset) <= 1e-6:
        return 0.0

    for obj in collection.all_objects:
        if obj.type == "MESH":
            obj.location.z += z_offset
    return z_offset


def terrain_top_surface_min_z(vertices: list[tuple[float, float, float]]) -> float:
    top_z_by_xy: dict[tuple[int, int], float] = {}
    xy_tolerance = 0.001
    for x, y, z in vertices:
        xy_key = (round(x / xy_tolerance), round(y / xy_tolerance))
        top_z_by_xy[xy_key] = max(top_z_by_xy.get(xy_key, z), z)
    return min(top_z_by_xy.values())


def align_collection_min_z_to_zero(collection: bpy.types.Collection) -> float:
    objects = [obj for obj in collection.all_objects if obj.type == "MESH"]
    if not objects:
        return 0.0

    min_z = min(
        (obj.matrix_world @ Vector(corner)).z
        for obj in objects
        for corner in obj.bound_box
    )
    if abs(min_z) <= 1e-6:
        return 0.0

    return apply_collection_z_offset(collection, -min_z)


def import_ifc_file(input_path: Path, remove_terrain: bool = True) -> tuple[int, str]:
    ifcopenshell, ifc_geom = ensure_ifcopenshell()

    # ifcopenshell.open() ist nicht in allen Builds PathLike-safe (C-Extension) → explizit str().
    ifc_file = ifcopenshell.open(str(input_path))
    root_collection = create_collection(f"{input_path.stem}_ifc", bpy.context.scene.collection)
    clear_collection_hierarchy(root_collection)

    scene_origin = scene_project_origin()
    ifc_map_transform = infer_ifc_map_transform(ifc_file)
    products = [
        product
        for product in ifc_file.by_type("IfcProduct")
        if getattr(product, "Representation", None) is not None
        and not product.is_a("IfcOpeningElement")
        and not product.is_a("IfcSpace")
    ]

    settings_primary = _build_ifc_geom_settings(ifc_geom, fallback=False)
    settings_fallback = _build_ifc_geom_settings(ifc_geom, fallback=True)

    imported = 0
    skipped_terrain = 0
    terrain_top_min_z: float | None = None
    first_error: str | None = None
    for product in products:
        try:
            shape = ifc_geom.create_shape(settings_primary, product)
        except Exception as exc:
            if first_error is None:
                first_error = str(exc)
            try:
                shape = ifc_geom.create_shape(settings_fallback, product)
            except Exception:
                continue

        geometry = shape.geometry
        try:
            raw_vertices = list(geometry.verts)
            raw_faces = list(geometry.faces)
        except Exception:
            continue

        if len(raw_vertices) == 0 or len(raw_faces) == 0:
            continue

        vertices = [
            (raw_vertices[i], raw_vertices[i + 1], raw_vertices[i + 2])
            for i in range(0, len(raw_vertices), 3)
        ]
        faces = [
            (raw_faces[i], raw_faces[i + 1], raw_faces[i + 2])
            for i in range(0, len(raw_faces), 3)
        ]

        blender_vertices = [
            ifc_vertex_to_scene_local(
                float(vertex[0]),
                float(vertex[1]),
                float(vertex[2]),
                scene_origin,
                ifc_map_transform,
            )
            for vertex in vertices
        ]

        if is_ifc_terrain_product(product):
            product_top_min_z = terrain_top_surface_min_z(blender_vertices)
            terrain_top_min_z = product_top_min_z if terrain_top_min_z is None else min(terrain_top_min_z, product_top_min_z)
            if remove_terrain:
                skipped_terrain += 1
                continue

        blender_faces = [tuple(int(index) for index in face) for face in faces]

        mesh_name = f"ifc_{product.id()}_{product.is_a()}"
        mesh = bpy.data.meshes.new(mesh_name)
        mesh.from_pydata(blender_vertices, [], blender_faces)
        mesh.update()

        object_name_value = product.Name or f"{product.is_a()}_{product.id()}"
        obj = bpy.data.objects.new(object_name_value, mesh)
        obj["ifc_id"] = int(product.id())
        obj["ifc_guid"] = str(getattr(product, "GlobalId", ""))
        obj["ifc_class"] = product.is_a()
        if is_ifc_terrain_product(product):
            obj["ifc_is_terrain"] = True
        obj["source_name"] = input_path.name
        if ifc_map_transform is not None:
            obj["ifc_georef_mode"] = "ifc_or_site"
        if scene_origin is not None:
            obj["crs_hint"] = bpy.context.scene.get(GEOSCENE_CRS_KEY, "EPSG:2056")
        root_collection.objects.link(obj)
        imported += 1

    if imported == 0:
        detail = f" Erstes IfcOpenShell-Error: {first_error}" if first_error else ""
        raise ParcelAddonError("Keine IFC-Geometrie importiert. Datei oder Geometrie konnte nicht verarbeitet werden." + detail)

    if terrain_top_min_z is not None:
        applied_z_offset = apply_collection_z_offset(root_collection, -terrain_top_min_z)
        root_collection["z0_reference"] = "ifc_terrain_top_min_z"
        root_collection["terrain_top_min_z_before_offset"] = float(terrain_top_min_z)
    else:
        applied_z_offset = align_collection_min_z_to_zero(root_collection)
        root_collection["z0_reference"] = "ifc_model_min_z_fallback"
    bpy.context.scene.parcel_workflow.last_ifc_import = str(input_path)
    if ifc_map_transform is not None:
        root_collection["georef_method"] = "IFC_to_GeoScene"
        root_collection["ifc_offset_e"] = ifc_map_transform["eastings"]
        root_collection["ifc_offset_n"] = ifc_map_transform["northings"]
        root_collection["ifc_offset_z"] = ifc_map_transform["height"]
    root_collection["z0_offset_applied"] = float(applied_z_offset)
    root_collection["terrain_objects_skipped"] = int(skipped_terrain)
    return imported, root_collection.name


def collection_bounds(collection: bpy.types.Collection) -> tuple[Vector, float]:
    objects = [obj for obj in collection.all_objects if obj.type in {"MESH", "CURVE", "EMPTY"}]
    if not objects:
        return Vector((0.0, 0.0, 0.0)), 10.0
    corners = []
    for obj in objects:
        for corner in obj.bound_box:
            corners.append(obj.matrix_world @ Vector(corner))
    min_corner = Vector((min(v.x for v in corners), min(v.y for v in corners), min(v.z for v in corners)))
    max_corner = Vector((max(v.x for v in corners), max(v.y for v in corners), max(v.z for v in corners)))
    center = (min_corner + max_corner) * 0.5
    radius = max((max_corner - min_corner).length * 0.6, 10.0)
    return center, radius


def focus_collection(collection_name: str) -> None:
    collection = bpy.data.collections.get(collection_name)
    if collection is None:
        raise ParcelAddonError("Keine importierte Collection zum Fokussieren gefunden.")
    center, radius = collection_bounds(collection)
    for window in bpy.context.window_manager.windows:
        for area in window.screen.areas:
            if area.type != "VIEW_3D":
                continue
            for space in area.spaces:
                if space.type != "VIEW_3D":
                    continue
                space.clip_start = 0.01
                space.clip_end = max(10000000.0, radius * 100.0)
                space.shading.type = "SOLID"
                region_3d = space.region_3d
                region_3d.view_perspective = "ORTHO"
                region_3d.view_rotation = (1.0, 0.0, 0.0, 0.0)
                region_3d.view_location = center
                region_3d.view_distance = max(radius * 2.5, 25.0)
    bpy.context.scene.cursor.location = center


def focus_named_object(object_name: str) -> None:
    obj = bpy.data.objects.get(object_name)
    if obj is None:
        raise ParcelAddonError(f"Objekt '{object_name}' nicht gefunden.")
    collection = bpy.data.collections.new("TEMP_FOCUS_COLLECTION")
    try:
        collection.objects.link(obj)
        center, radius = collection_bounds(collection)
    finally:
        bpy.data.collections.remove(collection)

    for window in bpy.context.window_manager.windows:
        for area in window.screen.areas:
            if area.type != "VIEW_3D":
                continue
            for space in area.spaces:
                if space.type != "VIEW_3D":
                    continue
                space.clip_start = 0.01
                space.clip_end = max(10000000.0, radius * 100.0)
                space.shading.type = "SOLID"
                region_3d = space.region_3d
                region_3d.view_perspective = "ORTHO"
                region_3d.view_rotation = (1.0, 0.0, 0.0, 0.0)
                region_3d.view_location = center
                region_3d.view_distance = max(radius * 2.5, 25.0)
    bpy.context.scene.cursor.location = center


def flatten_oereb_payload(payload: dict[str, Any]) -> dict[str, Any]:
    flattened: dict[str, Any] = {
        "requested_egrid": payload.get("requested_egrid"),
        "resolved_canton": payload.get("resolved_canton"),
        "service_url": payload.get("service_url"),
        "extract_url": payload.get("extract_url"),
        "primary_zone": payload.get("primary_zone"),
        "legend_count": len(payload.get("legend_entries") or []),
        "zone_count": len(payload.get("zones") or []),
        "source_layer": "oereb",
    }

    real_estate = payload.get("real_estate") or {}
    for key, value in real_estate.items():
        flattened[f"real_estate_{key}"] = value

    zones = payload.get("zones") or []
    for index, zone in enumerate(zones, start=1):
        flattened[f"zone_{index}_legend_text"] = zone.get("legend_text")
        flattened[f"zone_{index}_theme_text"] = zone.get("theme_text")
        flattened[f"zone_{index}_type_code"] = zone.get("type_code")
        flattened[f"zone_{index}_law_status"] = zone.get("law_status")
        flattened[f"zone_{index}_area_share"] = zone.get("area_share")
        flattened[f"zone_{index}_part_in_percent"] = zone.get("part_in_percent")

    legend_entries = payload.get("legend_entries") or []
    for index, entry in enumerate(legend_entries, start=1):
        flattened[f"legend_{index}_theme_text"] = entry.get("theme_text")
        flattened[f"legend_{index}_legend_text"] = entry.get("legend_text")
        flattened[f"legend_{index}_type_code"] = entry.get("type_code")
        flattened[f"legend_{index}_law_status"] = entry.get("law_status")
        flattened[f"legend_{index}_area_share"] = entry.get("area_share")
        flattened[f"legend_{index}_part_in_percent"] = entry.get("part_in_percent")

    flattened["legend_entries_json"] = payload.get("legend_entries") or []
    flattened["zones_json"] = payload.get("zones") or []
    return flattened


def egrid_from_geojson(geojson_path: Path) -> str | None:
    """Gibt das EGRID der Zielparzelle zurück (is_target_parcel=True),
    sonst das erste gültige EGRID in der Datei."""
    try:
        payload = json.loads(geojson_path.read_text(encoding="utf-8"))
    except Exception:
        return None
    features = payload.get("features") or []
    # Erst Zielparzelle suchen
    for feature in features:
        if not isinstance(feature, dict):
            continue
        props = feature.get("properties") or {}
        if props.get("is_target_parcel") in (True, 1, "1", "true", "True"):
            egrid = props.get("EGRIS_EGRID") or props.get("EGRID") or props.get("egrid")
            if egrid and len(str(egrid)) == 14 and str(egrid).upper().startswith("CH"):
                return str(egrid).upper()
    # Fallback: erstes gültiges EGRID
    for feature in features:
        if not isinstance(feature, dict):
            continue
        props = feature.get("properties") or {}
        egrid = props.get("EGRIS_EGRID") or props.get("EGRID") or props.get("egrid")
        if egrid and len(str(egrid)) == 14 and str(egrid).upper().startswith("CH"):
            return str(egrid).upper()
    return None


def import_oereb_point(egrid: str, collection_name: str, preferred_canton: str | None = None) -> tuple[str, str, str, list]:
    root_collection = bpy.data.collections.get(collection_name)
    if root_collection is None:
        raise ParcelAddonError("Keine importierte Collection fuer den OEREB-Punkt gefunden.")

    payload = fetch_oereb_payload(egrid, preferred_canton=preferred_canton)
    oereb_collection = create_collection("oereb", root_collection)
    clear_collection_objects(oereb_collection)

    center, _ = collection_bounds(root_collection)
    object_name_value = f"{egrid}_oereb"
    add_point_object(
        object_name_value,
        (float(center.x), float(center.y), float(center.z)),
        oereb_collection,
        flatten_oereb_payload(payload),
        "OEREB",
    )
    municipality = str((payload.get("real_estate") or {}).get("municipality") or "")
    zones = payload.get("zones") or []
    return object_name_value, str(payload.get("primary_zone") or "Keine Hauptzone gefunden"), municipality, zones


class ParcelWorkflowProperties(PropertyGroup):
    project_root: StringProperty(name="Projektordner", subtype="DIR_PATH", default="")
    canton: EnumProperty(name="Kanton", items=CANTON_ITEMS, default="TG")
    egrid: StringProperty(name="E-GRID", default="")
    gpkg_path: StringProperty(name="GeoPackage", subtype="FILE_PATH")
    geojson_path: StringProperty(name="GeoJSON", subtype="FILE_PATH")
    ifc_path: StringProperty(name="IFC", subtype="FILE_PATH")
    remove_ifc_terrain: BoolProperty(name="Terrain rauslöschen", default=True)
    last_import_collection: StringProperty(name="Import Collection", default="")
    docker_busy: BoolProperty(name="Docker aktiv", default=False)
    docker_status: StringProperty(name="Docker Status", default="Bereit.")
    last_docker_log: StringProperty(name="Docker Log", default="")
    last_downloaded_gpkg: StringProperty(name="Letztes Docker GPKG", subtype="FILE_PATH", default="")
    resolved_project_root: StringProperty(name="Erkannter Projektordner", subtype="DIR_PATH", default="")
    last_oereb_object: StringProperty(name="Letztes OEREB-Objekt", default="")
    last_oereb_zone: StringProperty(name="Letzte OEREB-Zone", default="")
    last_oereb_municipality: StringProperty(name="Letzte OEREB-Gemeinde", default="")
    last_nutzungszone: StringProperty(name="Nutzungszone", default="")
    selected_zone: EnumProperty(name="Bauzone", items=_zone_enum_items)
    gemeinde: StringProperty(name="Gemeinde", default="")
    last_origin_e: StringProperty(name="Origin E", default="")
    last_origin_n: StringProperty(name="Origin N", default="")
    last_origin_z: StringProperty(name="Origin Z", default="")
    last_ifc_import: StringProperty(name="Letzter IFC-Import", subtype="FILE_PATH", default="")
    adresse: StringProperty(name="Strasse + Ort", default="")
    action_mode: EnumProperty(
        name="Aktion",
        items=(
            ("CONVERT_IMPORT", "Umwandeln + Importieren", ""),
            ("CONVERT_ONLY", "Nur GeoJSON erzeugen", ""),
            ("IMPORT_ONLY", "Nur GeoJSON importieren", ""),
        ),
        default="CONVERT_IMPORT",
    )


class PARCELWORKFLOW_OT_run_docker(Operator):
    bl_idname = "parcel_workflow.run_docker"
    bl_label = "Docker Download starten"

    _timer = None
    _process = None
    _phase = ""
    _stdout_buffer = ""
    _result_payload: dict[str, Any] | None = None
    _spinner_index = 0
    _recent_logs: list[str] = []
    _start_time: float = 0.0

    def _remember_log(self, line: str) -> None:
        if not line:
            return
        self._recent_logs.append(line)
        if len(self._recent_logs) > 20:
            self._recent_logs = self._recent_logs[-20:]

    def _is_informational_log(self, line: str) -> bool:
        lowered = line.lower()
        return (
            lowered.startswith("view build details:")
            or lowered.startswith("what's next:")
            or lowered.startswith("docker scout quickview")
            or lowered.startswith("anzahl layer:")        # reine Statusinformation, kein Fehler
            or lowered.startswith("geopackage geladen:")
            or lowered.startswith("parzelle gefunden")
            or lowered.startswith("oereb-zonen gespeichert")
            or lowered.startswith("oereb-zonen konnten")
        )

    def _best_error_message(self, fallback: str) -> str:
        # 1. Echte Fehlermeldungen bevorzugen (Zeilen mit typischen Fehler-Präfixen)
        _error_prefixes = ("fehler:", "error:", "exception:", "traceback", "userfa")
        for line in reversed(self._recent_logs):
            ll = line.lower()
            if any(ll.startswith(p) for p in _error_prefixes):
                return line
        # 2. Letzter nicht-informativer Logeintrag
        for line in reversed(self._recent_logs):
            if not self._is_informational_log(line):
                return line
        return fallback

    def _cleanup(self, context) -> None:
        if self._timer is not None:
            context.window_manager.event_timer_remove(self._timer)
            self._timer = None
        self._process = None
        redraw_ui()

    def _set_status(self, props: ParcelWorkflowProperties, message: str) -> None:
        spinner = SPINNER_FRAMES[self._spinner_index % len(SPINNER_FRAMES)] if props.docker_busy else ""
        props.docker_status = f"{spinner} {message}".strip()
        redraw_ui()

    def _drain_output(self, props: ParcelWorkflowProperties, flush_tail: bool = False) -> None:
        if self._process is None or self._process.stdout is None:
            return
        try:
            chunk = os.read(self._process.stdout.fileno(), 65536)
        except BlockingIOError:
            chunk = b""
        except OSError:
            chunk = b""
        if chunk:
            self._stdout_buffer += chunk.decode("utf-8", errors="replace")

        if flush_tail:
            lines = self._stdout_buffer.splitlines()
            self._stdout_buffer = ""
        else:
            lines = self._stdout_buffer.splitlines()
            if self._stdout_buffer and not self._stdout_buffer.endswith(("\n", "\r")):
                self._stdout_buffer = lines.pop() if lines else self._stdout_buffer
            else:
                self._stdout_buffer = ""

        for raw_line in lines:
            line = raw_line.strip()
            if not line:
                continue
            self._remember_log(line)
            if not self._is_informational_log(line):
                props.last_docker_log = line
            if line.startswith("RESULT_JSON="):
                payload = line.split("=", 1)[1]
                try:
                    self._result_payload = json.loads(payload)
                except json.JSONDecodeError:
                    self._result_payload = None

    def _start_process(self, command: list[str], cwd: Path) -> None:
        self._stdout_buffer = ""
        self._recent_logs = []
        self._process = subprocess.Popen(
            command,
            cwd=str(cwd),
            env=docker_process_env(),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        if self._process.stdout is not None and os.name != "nt":
            os.set_blocking(self._process.stdout.fileno(), False)

    def _finish_success(self, context) -> set[str]:
        props = context.scene.parcel_workflow
        props.docker_busy = False

        parcel_gpkg = ""
        raw_oereb_json = ""
        if self._result_payload:
            raw_parcel_gpkg = str(self._result_payload.get("parcel_gpkg") or "")
            parcel_gpkg = map_container_data_path_to_host(raw_parcel_gpkg, self._project_root) if raw_parcel_gpkg else ""
            raw_oereb_json = str(self._result_payload.get("oereb_json") or "")

        if parcel_gpkg:
            props.last_downloaded_gpkg = parcel_gpkg
            props.gpkg_path = parcel_gpkg

            # OEREB-JSON laden (von Docker mitgeliefert)
            oereb_json_path: Path | None = None
            if raw_oereb_json:
                mapped = map_container_data_path_to_host(raw_oereb_json, self._project_root)
                candidate = Path(mapped)
                if candidate.exists():
                    oereb_json_path = candidate
            if oereb_json_path is None:
                egrid = props.egrid.strip().upper()
                if egrid:
                    candidate = Path(parcel_gpkg).with_name(f"{egrid}_oereb.json")
                    if candidate.exists():
                        oereb_json_path = candidate
            if oereb_json_path is not None:
                load_oereb_json(oereb_json_path, props)
                zone_count = len([z for z in _zone_cache if z[0] != "NONE"])
                props.docker_status = f"Fertig: {Path(parcel_gpkg).name} · {zone_count} Zonen"
            else:
                props.docker_status = f"Fertig: {Path(parcel_gpkg).name}"
            self.report({"INFO"}, f"Docker-Export abgeschlossen: {Path(parcel_gpkg).name}")
        else:
            props.docker_status = "Docker fertig, aber ohne lesbaren Ergebnis-Pfad."
            self.report({"WARNING"}, "Docker fertig, aber Ergebnis-Pfad konnte nicht gelesen werden.")

        self._cleanup(context)
        return {"FINISHED"}

    def _finish_error(self, context, message: str) -> set[str]:
        props = context.scene.parcel_workflow
        props.docker_busy = False
        props.docker_status = f"Fehler: {message}"
        self._cleanup(context)
        self.report({"ERROR"}, message)
        return {"CANCELLED"}

    def modal(self, context, event):
        props = context.scene.parcel_workflow

        if event.type != "TIMER":
            return {"PASS_THROUGH"}

        self._spinner_index = (self._spinner_index + 1) % len(SPINNER_FRAMES)
        self._drain_output(props)

        if self._process is None:
            return self._finish_error(context, "Docker-Prozess konnte nicht gestartet werden.")

        if self._process.poll() is None:
            elapsed = int(time.time() - self._start_time)
            phase_text = "Docker-Image wird gebaut" if self._phase == "build" else "GeoPackage wird geladen"
            elapsed_str = f" ({elapsed}s)"
            extra = f" | {props.last_docker_log}" if props.last_docker_log else ""
            self._set_status(props, f"{phase_text}{elapsed_str}{extra}")
            return {"RUNNING_MODAL"}

        self._drain_output(props, flush_tail=True)
        return_code = self._process.returncode
        if return_code != 0:
            detail = self._best_error_message(props.last_docker_log or f"Docker-Prozess beendet mit Code {return_code}")
            return self._finish_error(context, detail)

        if self._phase == "build":
            self._phase = "run"
            props.last_docker_log = ""
            self._set_status(props, "Container wird gestartet")
            self._start_process(self._run_command, self._project_root)
            return {"RUNNING_MODAL"}

        return self._finish_success(context)

    def execute(self, context):
        props = context.scene.parcel_workflow
        if props.docker_busy:
            self.report({"WARNING"}, "Docker laeuft bereits.")
            return {"CANCELLED"}
        docker_executable = resolve_docker_executable()
        if docker_executable is None:
            self.report({"ERROR"}, "Docker wurde nicht gefunden. Bitte Docker Desktop starten.")
            return {"CANCELLED"}

        egrid = props.egrid.strip().upper()
        if not props.canton:
            self.report({"ERROR"}, "Bitte einen Kanton auswaehlen.")
            return {"CANCELLED"}
        if len(egrid) != 14 or not egrid.startswith("CH") or not egrid[2:].isdigit():
            self.report({"ERROR"}, "Bitte eine gueltige E-GRID im Format CH + 12 Ziffern eingeben.")
            return {"CANCELLED"}

        project_root = resolve_project_root(props.project_root)
        if project_root is None:
            self.report(
                {"ERROR"},
                "Projektordner nicht gefunden. Bitte im Add-on den building-permit-boundary-check Ordner setzen.",
            )
            return {"CANCELLED"}

        props.resolved_project_root = str(project_root)
        self._project_root = project_root
        code_root = self._project_root / "CodeJonas"
        dockerfile_path = code_root / "Docker" / "Dockerfile"
        data_dir = code_root / "data"
        image_name = "parcel-workflow-lv95"

        if not dockerfile_path.exists():
            self.report({"ERROR"}, f"Dockerfile nicht gefunden: {dockerfile_path}")
            return {"CANCELLED"}

        data_dir.mkdir(parents=True, exist_ok=True)
        props.docker_busy = True
        props.last_docker_log = ""
        props.last_downloaded_gpkg = ""
        self._result_payload = None
        self._spinner_index = 0
        self._start_time = time.time()
        self._phase = "build"
        self._build_command = [
            docker_executable,
            "build",
            "--progress=plain",
            "-t",
            image_name,
            "-f",
            str(dockerfile_path),
            str(code_root),
        ]
        self._run_command = [
            docker_executable,
            "run",
            "--rm",
            "-e", f"API_LV95_CANTON={props.canton}",
            "-e", f"API_LV95_EGRID={egrid}",
            "-e", "PYTHONUNBUFFERED=1",   # stdout sofort flushen (kein Buffering in Docker)
            "-v", f"{data_dir}:/app/data",
            image_name,
            "python", "-u",              # -u = unbuffered stdin/stdout/stderr
            "Nutzbar/API_LVS95.py",
            "--json-output",
        ]

        try:
            self._start_process(self._build_command, self._project_root)
        except OSError as exc:
            props.docker_busy = False
            self.report({"ERROR"}, f"Docker konnte nicht gestartet werden: {exc}")
            return {"CANCELLED"}

        self._set_status(props, "Docker-Image wird gebaut")
        self._timer = context.window_manager.event_timer_add(0.2, window=context.window)
        context.window_manager.modal_handler_add(self)
        return {"RUNNING_MODAL"}


class PARCELWORKFLOW_OT_run(Operator):
    bl_idname = "parcel_workflow.run"
    bl_label = "Aktion ausfuehren"

    def _load_oereb_zones(self, egrid: str, props: Any, gpkg_path: Path | None) -> tuple[list[dict], str]:
        """Lädt OEREB-Zonen: zuerst _oereb.json (Docker), sonst direkt API.
        Gibt (zones, municipality) zurück. Filtert immer auf Zonen mit Flächenanteil > 0."""
        def _has_area(z: dict) -> bool:
            return (z.get("area_share") or 0) > 0 or (z.get("part_in_percent") or 0.0) > 0.0

        if gpkg_path:
            candidate = gpkg_path.with_name(f"{egrid}_oereb.json")
            if candidate.exists():
                try:
                    data = json.loads(candidate.read_text(encoding="utf-8"))
                    zones = [z for z in (data.get("zones") or []) if _has_area(z)]
                    if zones:
                        return zones, data.get("municipality") or ""
                except Exception:
                    pass
        try:
            payload = fetch_oereb_payload(egrid, preferred_canton=props.canton)
            zones = [z for z in (payload.get("zones") or []) if _has_area(z)]
            municipality = str((payload.get("real_estate") or {}).get("municipality") or "")
            return zones, municipality
        except Exception:
            return [], ""

    def _apply_oereb(self, zones: list[dict], municipality: str, props: Any) -> None:
        """Schreibt OEREB-Ergebnis in die Props und den Zone-Cache."""
        update_zone_cache(zones)
        props.last_oereb_zone = zones[0].get("legend_text") or "" if zones else ""
        props.last_oereb_municipality = municipality
        if municipality:
            props.gemeinde = municipality
        # Nur Nutzungsplanung-Zonen als Info-Text (ch.Nutzungsplanung und kantonale Varianten)
        nutzungszonen = [
            z.get("legend_text") or ""
            for z in zones
            if "nutzungsplanung" in (z.get("theme_code") or "").lower()
        ]
        props.last_nutzungszone = ", ".join(z for z in nutzungszonen if z)

    def execute(self, context):
        props = context.scene.parcel_workflow

        for name in ("Cube", "Camera", "Light"):
            obj = bpy.data.objects.get(name)
            if obj is not None:
                bpy.data.objects.remove(obj, do_unlink=True)

        try:
            if props.action_mode in {"CONVERT_IMPORT", "CONVERT_ONLY"}:
                if not props.gpkg_path:
                    self.report({"ERROR"}, "Bitte zuerst eine GPKG-Datei waehlen.")
                    return {"CANCELLED"}
                input_path = Path(bpy.path.abspath(props.gpkg_path))
                if not input_path.exists():
                    self.report({"ERROR"}, f"Datei nicht gefunden: {input_path}")
                    return {"CANCELLED"}
                output_path = Path(bpy.path.abspath(props.geojson_path)) if props.geojson_path else input_path.with_name(f"{input_path.stem}_resf.geojson")
                feature_count, layer_names = gpkg_to_geojson(input_path, output_path, only_resf=True, include_hadr=True)
                props.geojson_path = str(output_path)

                # EGRID aus GeoJSON lesen und OEREB als Metadaten anhängen
                extracted_egrid = egrid_from_geojson(output_path)
                if extracted_egrid:
                    props.egrid = extracted_egrid
                egrid_for_convert = extracted_egrid or props.egrid.strip().upper()
                if egrid_for_convert:
                    zones, municipality = self._load_oereb_zones(egrid_for_convert, props, input_path)
                    # Gemeinde aus GeoJSON-Features wenn OEREB keine hat
                    if not municipality:
                        municipality = municipality_from_geojson(output_path)
                    if zones:
                        append_oereb_to_geojson(output_path, zones, egrid_for_convert, municipality)
                        self._apply_oereb(zones, municipality, props)
                    elif municipality:
                        props.gemeinde = municipality
                        props.last_oereb_municipality = municipality

                if props.action_mode == "CONVERT_ONLY":
                    joined_names = ", ".join(layer_names)
                    self.report({"INFO"}, f"{feature_count} Features aus '{joined_names}' + OEREB nach GeoJSON exportiert.")
                    return {"FINISHED"}

            if props.action_mode in {"CONVERT_IMPORT", "IMPORT_ONLY"}:
                if not props.geojson_path:
                    self.report({"ERROR"}, "Bitte zuerst eine GeoJSON-Datei angeben oder erzeugen.")
                    return {"CANCELLED"}
                geojson_path = Path(bpy.path.abspath(props.geojson_path))
                if not geojson_path.exists():
                    self.report({"ERROR"}, f"Datei nicht gefunden: {geojson_path}")
                    return {"CANCELLED"}

                # OEREB laden: _oereb.json hat Vorrang vor gespeicherten GeoJSON-Metadaten,
                # da die GeoJSON-Datei u.U. noch Daten aus einem früheren Durchlauf enthält.
                extracted_egrid = egrid_from_geojson(geojson_path)
                if extracted_egrid:
                    props.egrid = extracted_egrid
                egrid_for_oereb = extracted_egrid or props.egrid.strip().upper()
                existing_zones: list[dict] = []
                if egrid_for_oereb:
                    gpkg_for_lookup = Path(bpy.path.abspath(props.gpkg_path)) if props.gpkg_path else None
                    fresh_zones, municipality = self._load_oereb_zones(egrid_for_oereb, props, gpkg_for_lookup)
                    if fresh_zones:
                        # GeoJSON-Metadaten immer mit aktuellen Daten überschreiben
                        append_oereb_to_geojson(geojson_path, fresh_zones, egrid_for_oereb, municipality)
                        existing_zones = fresh_zones
                if not existing_zones:
                    # Fallback: bereits gespeicherte Metadaten in der GeoJSON verwenden
                    existing_zones = zones_from_geojson(geojson_path)

                # Bestehende Collection der gleichen Parzelle löschen (verhindert .001-Duplikate)
                if egrid_for_oereb:
                    for coll_name in list(bpy.data.collections.keys()):
                        if egrid_for_oereb in coll_name:
                            coll = bpy.data.collections[coll_name]
                            # Alle Mesh-Objekte der Collection entfernen
                            for obj in list(coll.objects):
                                bpy.data.objects.remove(obj, do_unlink=True)
                            # Collection selbst entfernen
                            bpy.data.collections.remove(coll)

                imported_count, collection_name = import_geojson(geojson_path)

                # Adresse aus HADR-Feature (Strassenname, Hausnummer, PLZ, Ortschaftsname)
                if not props.adresse:
                    addr = address_from_geojson(geojson_path)
                    if addr:
                        props.adresse = addr

                # Gemeinde: zuerst aus OEREB, sonst aus GeoJSON-Features (hadr.Ortschaftsname)
                municipality = (json.loads(geojson_path.read_text(encoding="utf-8")).get("oereb") or {}).get("municipality") or ""
                if not municipality:
                    municipality = municipality_from_geojson(geojson_path)
                if existing_zones:
                    self._apply_oereb(existing_zones, municipality, props)
                elif municipality:
                    props.gemeinde = municipality
                    props.last_oereb_municipality = municipality

                # Räumliche Überprüfung überschreibt OEREB-Gemeindewert:
                # OEREB (TG und andere Kantone) liefert manchmal den Ortschaftsnamen
                # (z.B. "Märwil") statt den korrekten Gemeindenamen ("Affeltrangen").
                # SwissBOUNDARIES3D-Identify über GeoAdmin gibt immer den echten Gemeindenamen.
                if props.last_origin_e and props.last_origin_n:
                    try:
                        spatial_gde = _municipality_from_lv95_coords(
                            float(props.last_origin_e), float(props.last_origin_n)
                        )
                        if spatial_gde:
                            props.gemeinde = spatial_gde
                            props.last_oereb_municipality = spatial_gde
                    except Exception:
                        pass

                self.report({"INFO"}, f"{imported_count} Objekte importiert in Collection '{collection_name}'.")
        except ParcelAddonError as exc:
            self.report({"ERROR"}, str(exc))
            return {"CANCELLED"}
        except (urllib.error.URLError, TimeoutError, ET.ParseError) as exc:
            self.report({"ERROR"}, f"OEREB-Abfrage fehlgeschlagen: {exc}")
            return {"CANCELLED"}

        return {"FINISHED"}


class PARCELWORKFLOW_OT_open_bauverordnung(Operator):
    bl_idname = "parcel_workflow.open_bauverordnung"
    bl_label = "Bauverordnung suchen"

    def execute(self, context):
        props = context.scene.parcel_workflow

        # 1) Gemeinde ermitteln
        gemeinde = props.gemeinde.strip()
        if not gemeinde and props.geojson_path:
            geojson_path = Path(bpy.path.abspath(props.geojson_path))
            if geojson_path.exists():
                gemeinde = municipality_from_geojson(geojson_path)
                if gemeinde:
                    props.gemeinde = gemeinde

        if not gemeinde:
            self.report({"WARNING"}, "Keine Gemeinde gefunden – bitte zuerst Parzelle importieren.")
            return {"CANCELLED"}

        # 2) Kanton ermitteln: aus GeoJSON-Feature (Feld "Kanton") oder props.canton
        canton_abbr = props.canton
        if props.geojson_path:
            geojson_path = Path(bpy.path.abspath(props.geojson_path))
            if geojson_path.exists():
                try:
                    payload = json.loads(geojson_path.read_text(encoding="utf-8"))
                    for feat in payload.get("features") or []:
                        kanton = (feat.get("properties") or {}).get("Kanton") or ""
                        if kanton:
                            canton_abbr = kanton.upper()
                            break
                except Exception:
                    pass
        canton_terrara = CANTON_TO_TERRARA.get(canton_abbr, canton_abbr)

        # 3) Direkte PDF-URL auf terrara.ch öffnen
        # Hinweis: terrara.ch schreibt "gemainde" (Tippfehler im API), muss so bleiben
        url = f"https://terrara.ch/servepdf.php?gemainde={gemeinde}&canton={canton_terrara}"
        self.report({"INFO"}, f"Öffne: {url}")
        webbrowser.open(url)
        return {"FINISHED"}


class PARCELWORKFLOW_OT_import_ifc(Operator):
    bl_idname = "parcel_workflow.import_ifc"
    bl_label = "IFC importieren"

    def execute(self, context):
        props = context.scene.parcel_workflow
        ifc_path_raw = props.ifc_path.strip()
        if not ifc_path_raw:
            self.report({"ERROR"}, "Bitte zuerst eine IFC-Datei waehlen.")
            return {"CANCELLED"}

        ifc_path = Path(bpy.path.abspath(ifc_path_raw))
        if not ifc_path.exists():
            self.report({"ERROR"}, f"Datei nicht gefunden: {ifc_path}")
            return {"CANCELLED"}

        try:
            imported_count, collection_name = import_ifc_file(ifc_path, remove_terrain=props.remove_ifc_terrain)
        except ParcelAddonError as exc:
            self.report({"ERROR"}, str(exc))
            return {"CANCELLED"}
        except Exception as exc:
            self.report({"ERROR"}, f"IFC-Import fehlgeschlagen: {exc}")
            return {"CANCELLED"}

        props.last_ifc_import = str(ifc_path)
        self.report({"INFO"}, f"{imported_count} IFC-Objekte importiert in Collection '{collection_name}'.")
        return {"FINISHED"}


# ══════════════════════════════════════════════════════════════════════════════
# GRENZABSTAND-CHECK (integriert aus boundary-check_v7.py)
# ══════════════════════════════════════════════════════════════════════════════

_VIS_COLLECTION    = "Grenzcheck_Visualisierung"
_EXCL_COLLECTIONS  = {"hadr"}
_COLOR_BUILDING    = (0.0,  0.7,  1.0,  0.30)
_COLOR_OK          = (0.05, 0.8,  0.1,  0.25)
_COLOR_VIOLATION   = (1.0,  0.08, 0.05, 0.40)
_COLOR_MAIN        = (1.0,  0.75, 0.0,  0.30)


# ── Geometrie-Hilfsfunktionen ─────────────────────────────────────────────────

def _gc_bbox_world(obj):
    corners = [obj.matrix_world @ Vector(c) for c in obj.bound_box]
    mn = Vector((min(c.x for c in corners), min(c.y for c in corners), min(c.z for c in corners)))
    mx = Vector((max(c.x for c in corners), max(c.y for c in corners), max(c.z for c in corners)))
    return mn, mx


def _gc_combined_aabb(objects):
    all_corners = []
    for obj in objects:
        for c in obj.bound_box:
            all_corners.append(obj.matrix_world @ Vector(c))
    if not all_corners:
        return None, None
    mn = Vector((min(c.x for c in all_corners), min(c.y for c in all_corners), min(c.z for c in all_corners)))
    mx = Vector((max(c.x for c in all_corners), max(c.y for c in all_corners), max(c.z for c in all_corners)))
    return mn, mx


def _gc_combined_aabb_clipped(objects, p_mn, p_mx, margin=0.15):
    clipped = []
    for obj in objects:
        o_mn, o_mx = _gc_bbox_world(obj)
        cx_mn = max(o_mn.x, p_mn.x - margin); cx_mx = min(o_mx.x, p_mx.x + margin)
        cy_mn = max(o_mn.y, p_mn.y - margin); cy_mx = min(o_mx.y, p_mx.y + margin)
        if cx_mn < cx_mx and cy_mn < cy_mx:
            clipped.append(Vector((cx_mn, cy_mn, o_mn.z)))
            clipped.append(Vector((cx_mx, cy_mx, o_mx.z)))
    if not clipped:
        return _gc_combined_aabb(objects)
    mn = Vector((min(c.x for c in clipped), min(c.y for c in clipped), min(c.z for c in clipped)))
    mx = Vector((max(c.x for c in clipped), max(c.y for c in clipped), max(c.z for c in clipped)))
    return mn, mx


def _gc_aabb_dist_xy(b_min, b_max, p_min, p_max):
    dx = max(b_min.x - p_max.x, p_min.x - b_max.x, 0.0)
    dy = max(b_min.y - p_max.y, p_min.y - b_max.y, 0.0)
    return math.sqrt(dx*dx + dy*dy)


def _gc_mesh_verts_xy(obj):
    if not obj.data or not hasattr(obj.data, 'vertices'):
        return []
    mat = obj.matrix_world
    return [Vector((mat @ v.co).xy) for v in obj.data.vertices]


def _gc_make_hull(pts):
    if len(pts) < 3:
        return pts
    return [pts[i] for i in convex_hull_2d(pts)]


def _gc_pt_seg_dist(px, py, ax, ay, bx, by):
    dx, dy = bx - ax, by - ay
    ls = dx*dx + dy*dy
    if ls < 1e-12:
        return math.sqrt((px-ax)**2 + (py-ay)**2)
    t = max(0.0, min(1.0, ((px-ax)*dx + (py-ay)*dy) / ls))
    return math.sqrt((px - ax - t*dx)**2 + (py - ay - t*dy)**2)


def _gc_pt_seg_orth(px, py, ax, ay, bx, by):
    dx, dy = bx - ax, by - ay
    ls = dx*dx + dy*dy
    if ls < 1e-12:
        return float('inf'), False
    t = ((px-ax)*dx + (py-ay)*dy) / ls
    if t < 0.0 or t > 1.0:
        return float('inf'), False
    cx, cy = ax + t*dx, ay + t*dy
    return math.sqrt((px-cx)**2 + (py-cy)**2), True


def _gc_parcel_boundary_segs(obj):
    mesh = obj.data
    if not mesh or not hasattr(mesh, 'polygons'):
        return []
    mat = obj.matrix_world
    vs  = mesh.vertices
    efc = {}
    for face in mesh.polygons:
        vv = list(face.vertices)
        for i in range(len(vv)):
            key = tuple(sorted((vv[i], vv[(i+1) % len(vv)])))
            efc[key] = efc.get(key, 0) + 1
    return [(Vector((mat @ vs[a].co).xy), Vector((mat @ vs[b].co).xy))
            for (a, b), cnt in efc.items() if cnt == 1]


def _gc_building_hull(objects, p_mn, p_mx, margin=0.15):
    pts = []
    for obj in objects:
        for v in _gc_mesh_verts_xy(obj):
            if p_mn.x-margin <= v.x <= p_mx.x+margin and p_mn.y-margin <= v.y <= p_mx.y+margin:
                pts.append(v)
    return _gc_make_hull(pts) if len(pts) >= 3 else []


def _gc_parcel_hull_clipped(parcel_obj, p_mn, p_mx, margin=20.0):
    pts = [v for v in _gc_mesh_verts_xy(parcel_obj)
           if p_mn.x-margin <= v.x <= p_mx.x+margin and p_mn.y-margin <= v.y <= p_mx.y+margin]
    if len(pts) < 2:
        all_pts = _gc_mesh_verts_xy(parcel_obj)
        cx, cy = (p_mn.x+p_mx.x)*0.5, (p_mn.y+p_mx.y)*0.5
        pts = sorted(all_pts, key=lambda v: (v.x-cx)**2 + (v.y-cy)**2)[:4]
    if len(pts) < 2:
        return []
    if len(pts) == 2:
        return pts
    return _gc_make_hull(pts)


def _gc_compute_grenzabstand(bldg_hull, own_parcel, neighbors):
    own_segs = _gc_parcel_boundary_segs(own_parcel)
    if not own_segs or not bldg_hull:
        return {nb: None for nb in neighbors}
    p_mn, p_mx = _gc_bbox_world(own_parcel)
    nb_hulls   = {nb: _gc_parcel_hull_clipped(nb, p_mn, p_mx) for nb in neighbors}
    distances  = {nb: float('inf') for nb in neighbors}
    n_bh       = len(bldg_hull)
    for seg_a, seg_b in own_segs:
        mx_pt = (seg_a.x+seg_b.x)*0.5; my_pt = (seg_a.y+seg_b.y)*0.5
        nearest_nb, nearest_d = None, float('inf')
        for nb, hull in nb_hulls.items():
            if not hull:
                continue
            for i in range(len(hull)):
                h1, h2 = hull[i], hull[(i+1) % len(hull)]
                d = _gc_pt_seg_dist(mx_pt, my_pt, h1.x, h1.y, h2.x, h2.y)
                if d < nearest_d:
                    nearest_d = d; nearest_nb = nb
        if nearest_nb is None:
            continue
        for p in bldg_hull:
            d, ok = _gc_pt_seg_orth(p.x, p.y, seg_a.x, seg_a.y, seg_b.x, seg_b.y)
            if ok and d < distances[nearest_nb]:
                distances[nearest_nb] = d
        for pt in (seg_a, seg_b):
            for i in range(n_bh):
                h1, h2 = bldg_hull[i], bldg_hull[(i+1) % n_bh]
                d, ok = _gc_pt_seg_orth(pt.x, pt.y, h1.x, h1.y, h2.x, h2.y)
                if ok and d < distances[nearest_nb]:
                    distances[nearest_nb] = d
    return {nb: (d if d != float('inf') else None) for nb, d in distances.items()}


# ── Objekt-Erkennung ──────────────────────────────────────────────────────────

_GC_TARGET_MARKER   = "resf_target_"
_GC_NEIGHBOR_MARKER = "_resf_"


def _gc_in_excl_collection(obj):
    return bool({col.name for col in obj.users_collection} & _EXCL_COLLECTIONS)


def _gc_find_target_parcel(scene):
    for o in scene.objects:
        if _GC_TARGET_MARKER in o.name and not _gc_in_excl_collection(o) and not o.get("grenzabstand_viz"):
            return o
    return None


def _gc_find_neighbors(scene):
    return [o for o in scene.objects
            if _GC_NEIGHBOR_MARKER in o.name
            and _GC_TARGET_MARKER not in o.name
            and not _gc_in_excl_collection(o)
            and not o.get("grenzabstand_viz")]


def _gc_get_buildings(scene, keyword):
    for col in bpy.data.collections:
        if keyword in col.name:
            return list(col.objects)
    return []


def _gc_short(name, n=38):
    return ("..." + name[-n:]) if len(name) > n else name


# ── Haupt-Prüfungslogik ───────────────────────────────────────────────────────

def _gc_run_check(keyword, g_gross, g_klein, lines):
    scene    = bpy.context.scene
    own      = _gc_find_target_parcel(scene)
    neighbors = _gc_find_neighbors(scene)
    buildings = _gc_get_buildings(scene, keyword)
    if own is None:
        lines.append("⚠  Keine Bauparzelle gefunden ('resf_target_' im Namen erwartet).")
        return
    if not neighbors:
        lines.append("⚠  Keine Nachbarparzellen gefunden.")
        return
    if not buildings:
        lines.append(f"⚠  Keine Gebäudeteile in Collection mit '{keyword}' gefunden.")
        return
    p_mn, p_mx = _gc_bbox_world(own)
    bldg_hull  = _gc_building_hull(buildings, p_mn, p_mx)
    use_poly   = bool(bldg_hull)
    lines.append(f"Bauparzelle     : {_gc_short(own.name)}")
    lines.append(f"Nachbarparzellen: {len(neighbors)}")
    lines.append(f"Gebäude         : {len(buildings)} Teile ('{keyword}')")
    lines.append(f"Methode         : {'Polygon' if use_poly else 'AABB (Fallback)'}")
    lines.append(f"Grenzabstand groß : {g_gross} m  |  klein: {g_klein} m")
    lines.append("─" * 60)
    lines.append("[ LAGE-CHECK ]")
    tol = 0.05
    if use_poly:
        inside = all(p_mn.x-tol <= v.x <= p_mx.x+tol and p_mn.y-tol <= v.y <= p_mx.y+tol for v in bldg_hull)
    else:
        bm, bx = _gc_combined_aabb_clipped(buildings, p_mn, p_mx)
        inside  = bm and (bm.x >= p_mn.x-tol and bx.x <= p_mx.x+tol and bm.y >= p_mn.y-tol and bx.y <= p_mx.y+tol)
    lines.append("  ✓ Gebäude liegt auf der Parzelle." if inside else "  ✗ Gebäude liegt AUSSERHALB!")
    if not inside:
        lines.append("  ✗  NEGATIVE PRÜFUNG"); return
    lines.append("─" * 60)
    if use_poly:
        raw = _gc_compute_grenzabstand(bldg_hull, own, neighbors)
    else:
        bm2, bx2 = _gc_combined_aabb_clipped(buildings, p_mn, p_mx)
        raw = {nb: _gc_aabb_dist_xy(bm2, bx2, *_gc_bbox_world(nb)) for nb in neighbors}
    gdist = {nb: (raw.get(nb) or 0.0) for nb in neighbors}
    def _nb_lbl(obj):
        """Gibt das EGRID der Nachbarparzelle zurück (eindeutiger Bezeichner für result_text).

        Priorität:
        1) Custom-Property EGRIS_EGRID / EGRID / egrid  (aus dem GeoJSON-Feature)
           → zuverlässigster Weg, nicht vom Dateinamen-Prefix beeinflusst
        2) Regex CH\\d{12} auf den Objekt-Namen (Fallback)
        3) Kurzname
        """
        for key in ("EGRIS_EGRID", "EGRID", "egrid"):
            val = str(obj.get(key) or "").strip().upper()
            if val and re.match(r'CH\d{9,}', val):
                return val
        eg = _gc_egrid_from_name(obj.name)
        return eg if eg else _gc_short(obj.name, 28)

    lines.append(f"[ SCHRITT 1 – Grosser Grenzabstand {g_gross} m ]")
    for nb in neighbors:
        d = gdist[nb]
        sym = "✓" if d >= g_gross else "✗"
        lines.append(f"  {sym} {_nb_lbl(nb):30s}  {d:.2f} m")
    ok_nb = [nb for nb, d in gdist.items() if d >= g_gross]
    if not ok_nb:
        lines.append("═" * 60); lines.append("ZUSAMMENFASSUNG")
        lines.append("  ✗  Kein Nachbar erfüllt den grossen Grenzabstand."); return
    haupt = max(ok_nb, key=lambda nb: gdist[nb])
    lines.append(f"  ✓  HAUPTWOHNSEITE: {_nb_lbl(haupt)}  {gdist[haupt]:.2f} m")
    lines.append("─" * 60)
    remaining = [nb for nb in neighbors if nb is not haupt]
    lines.append(f"[ SCHRITT 2 – Kleiner Grenzabstand {g_klein} m ]")
    violations = []
    for nb in remaining:
        d = gdist[nb]; ok = d >= g_klein
        sym = "✓" if ok else "✗"
        lines.append(f"  {sym} {_nb_lbl(nb):30s}  {d:.2f} m")
        if not ok:
            violations.append((_nb_lbl(nb), d, g_klein-d))
    lines.append("═" * 60); lines.append("ZUSAMMENFASSUNG"); lines.append("═" * 60)
    lines.append(f"  Hauptwohnseite : {_nb_lbl(haupt)}  {gdist[haupt]:.2f} m  ✓")
    if not violations:
        lines.append(f"  Klein-Abstand  : alle Seiten >= {g_klein} m  ✓")
        lines.append("  ✓  POSITIVE PRÜFUNG – Bauvorhaben zulaessig.")
    else:
        lines.append("  Klein-Abstand  : ✗  VERLETZT bei:")
        for pn, d, fehlt in violations:
            lines.append(f"     {pn}  {d:.2f} m  (fehlt {fehlt:.2f} m)")
        lines.append("  ✗  NEGATIVE PRÜFUNG – Grenzabstand nicht eingehalten!")


# ── Visualisierungs-Hilfsfunktionen ──────────────────────────────────────────

def _gc_vis_collection(scene):
    c = bpy.data.collections.get(_VIS_COLLECTION)
    if c is None:
        c = bpy.data.collections.new(_VIS_COLLECTION)
        scene.collection.children.link(c)
    return c


def _gc_clear_vis(scene):
    c = bpy.data.collections.get(_VIS_COLLECTION)
    if not c:
        return
    for obj in list(c.objects):
        if obj.get("grenzabstand_viz"):
            mesh = obj.data
            bpy.data.objects.remove(obj, do_unlink=True)
            if mesh and mesh.users == 0:
                bpy.data.meshes.remove(mesh)


def _gc_material(color_rgba):
    r, g, b, a = color_rgba
    name = f"_GrenzViz_{int(r*255):03d}_{int(g*255):03d}_{int(b*255):03d}"
    mat  = bpy.data.materials.get(name)
    if mat is None:
        mat = bpy.data.materials.new(name)
        mat.use_nodes = True
        mat.blend_method = 'BLEND'
        if hasattr(mat, 'shadow_method'):
            mat.shadow_method = 'NONE'
        # diffuse_color = Viewport-Farbe im SOLID-Modus (MATERIAL color type)
        mat.diffuse_color = (r, g, b, a)
        bsdf = mat.node_tree.nodes.get("Principled BSDF")
        if bsdf:
            bsdf.inputs["Base Color"].default_value = (r, g, b, 1.0)
            bsdf.inputs["Alpha"].default_value      = a
            bsdf.inputs["Roughness"].default_value  = 0.8
            # Leichte Emission → Farbe auch im SOLID-Modus sichtbar
            if "Emission Color" in bsdf.inputs:
                bsdf.inputs["Emission Color"].default_value    = (r, g, b, 1.0)
                bsdf.inputs["Emission Strength"].default_value = 0.15
    return mat


def _gc_flat_polygon(name, pts_xy, z, color, coll):
    if not pts_xy or len(pts_xy) < 3:
        return None
    old = bpy.data.objects.get(name)
    if old:
        m = old.data; bpy.data.objects.remove(old, do_unlink=True)
        if m and m.users == 0:
            bpy.data.meshes.remove(m)
    verts = [(p.x, p.y, z) for p in pts_xy]
    n     = len(pts_xy)
    faces = [(0, i, i+1) for i in range(1, n-1)]
    mesh  = bpy.data.meshes.new(name)
    mesh.from_pydata(verts, [], faces); mesh.update()
    mesh.materials.append(_gc_material(color))
    r, g, b, a = color
    obj = bpy.data.objects.new(name, mesh)
    obj.display_type = 'SOLID'
    obj.show_wire    = True
    obj.hide_select  = True
    # obj.color → wird im SOLID-Modus mit color_type='OBJECT' angezeigt
    obj.color        = (r, g, b, 1.0)
    obj["grenzabstand_viz"] = True
    coll.objects.link(obj)
    return obj


# ── Grenzcheck-Properties ─────────────────────────────────────────────────────

class GrenzcheckProperties(PropertyGroup):
    collection_keyword: StringProperty(
        name="IFC-Collection",
        default="_parcel_ifc",
        description="Stichwort im Collection-Namen der importierten IFC-Gebäudeteile"
    )
    grenzabstand_gross: FloatProperty(name="Hauptwohnseite (m)", default=6.0, min=0.0, max=50.0)
    grenzabstand_klein: FloatProperty(name="Übrige Seiten (m)",  default=3.0, min=0.0, max=50.0)
    result_text: StringProperty(default="")
    last_pdf_path: StringProperty(name="Letztes PDF", subtype="FILE_PATH", default="")
    pdf_status: StringProperty(name="PDF-Status", default="")


# ── Grenzcheck-Operatoren ─────────────────────────────────────────────────────

class GRENZCHECK_OT_run(Operator):
    bl_idname    = "parcel_workflow.grenzcheck_run"
    bl_label     = "Grenzabstand prüfen"
    bl_description = "Zweistufige Grenzabstandsprüfung (Polygon-basiert)"

    def execute(self, context):
        props = context.scene.grenzcheck_props
        if props.grenzabstand_klein >= props.grenzabstand_gross:
            self.report({'WARNING'}, "Kleiner Grenzabstand muss kleiner sein als der grosse!")
            return {'CANCELLED'}
        lines = []
        _gc_run_check(props.collection_keyword, props.grenzabstand_gross, props.grenzabstand_klein, lines)
        props.result_text = "\n".join(lines)
        def draw_popup(self_inner, ctx):
            for line in lines:
                self_inner.layout.label(text=line)
        context.window_manager.popup_menu(draw_popup, title="Grenzabstand-Prüfung", icon='INFO')
        return {'FINISHED'}


class GRENZCHECK_OT_visualize(Operator):
    bl_idname    = "parcel_workflow.grenzcheck_visualize"
    bl_label     = "Visualisieren"
    bl_description = "Farbige Polygon-Overlays: Cyan=Gebäude, Grün=OK, Rot=Verletzt, Gold=Hauptwohnseite"

    def execute(self, context):
        props = context.scene.grenzcheck_props
        scene = context.scene
        if not props.result_text:
            self.report({'WARNING'}, "Bitte zuerst 'Grenzabstand prüfen' ausführen!")
            return {'CANCELLED'}
        own       = _gc_find_target_parcel(scene)
        neighbors = _gc_find_neighbors(scene)
        buildings = _gc_get_buildings(scene, props.collection_keyword)
        if not own or not neighbors or not buildings:
            self.report({'WARNING'}, "Objekte nicht gefunden – zuerst Parzelle + IFC importieren.")
            return {'CANCELLED'}
        coll = _gc_vis_collection(scene)
        _gc_clear_vis(scene)
        for area in context.screen.areas:
            if area.type == 'VIEW_3D':
                for space in area.spaces:
                    if space.type == 'VIEW_3D':
                        space.shading.color_type = 'OBJECT'
        p_mn, p_mx = _gc_bbox_world(own)
        z = p_mn.z + 0.05
        bldg_hull  = _gc_building_hull(buildings, p_mn, p_mx)
        bm, bx     = _gc_combined_aabb_clipped(buildings, p_mn, p_mx)
        if bldg_hull:
            _gc_flat_polygon("_VIS_Gebäude", bldg_hull, z+0.02, _COLOR_BUILDING, coll)
            raw = _gc_compute_grenzabstand(bldg_hull, own, neighbors)
        else:
            # Fallback: AABB-Rechteck als Gebäude-Footprint
            if bm and bx:
                rect = [Vector((bm.x, bm.y)), Vector((bx.x, bm.y)),
                        Vector((bx.x, bx.y)), Vector((bm.x, bx.y))]
                _gc_flat_polygon("_VIS_Gebäude", rect, z+0.02, _COLOR_BUILDING, coll)
            raw = {nb: _gc_aabb_dist_xy(bm, bx, *_gc_bbox_world(nb)) for nb in neighbors}
        gdist  = {nb: (raw.get(nb) or 0.0) for nb in neighbors}
        ok_nb  = [nb for nb, d in gdist.items() if d >= props.grenzabstand_gross]
        haupt  = max(ok_nb, key=lambda nb: gdist[nb]) if ok_nb else None
        for nb in neighbors:
            if nb is haupt:
                color = _COLOR_MAIN
            else:
                color = _COLOR_VIOLATION if gdist[nb] < props.grenzabstand_klein else _COLOR_OK
            hull = _gc_parcel_hull_clipped(nb, p_mn, p_mx)
            name = f"_VIS_Parzelle_{nb.name[:26]}"
            if hull and len(hull) >= 3:
                _gc_flat_polygon(name, hull, z, color, coll)
            else:
                # Fallback: AABB-Rechteck der Nachbarparzelle
                nb_mn, nb_mx = _gc_bbox_world(nb)
                rect = [Vector((nb_mn.x, nb_mn.y)), Vector((nb_mx.x, nb_mn.y)),
                        Vector((nb_mx.x, nb_mx.y)), Vector((nb_mn.x, nb_mx.y))]
                _gc_flat_polygon(name, rect, z, color, coll)
        self.report({'INFO'}, f"Visualisierung erstellt ({_VIS_COLLECTION}).")
        return {'FINISHED'}


class GRENZCHECK_OT_clear_vis(Operator):
    bl_idname = "parcel_workflow.grenzcheck_clear_vis"
    bl_label  = "Visualisierung löschen"

    def execute(self, context):
        _gc_clear_vis(context.scene)
        for area in context.screen.areas:
            if area.type == 'VIEW_3D':
                for space in area.spaces:
                    if space.type == 'VIEW_3D':
                        space.shading.color_type = 'MATERIAL'
        self.report({'INFO'}, "Visualisierung gelöscht.")
        return {'FINISHED'}


class GRENZCHECK_OT_clear(Operator):
    bl_idname = "parcel_workflow.grenzcheck_clear"
    bl_label  = "Ergebnis löschen"

    def execute(self, context):
        props = context.scene.grenzcheck_props
        props.result_text  = ""
        props.last_pdf_path = ""
        props.pdf_status   = ""
        return {'FINISHED'}


# ── PDF-Export Hilfsfunktionen (portiert aus Download-Version) ────────────────

def ensure_reportlab():
    try:
        from reportlab.lib import colors
        from reportlab.lib.pagesizes import A4
        from reportlab.lib.utils import ImageReader
        from reportlab.pdfbase import pdfmetrics
        from reportlab.pdfgen import canvas
        return {"canvas": canvas, "A4": A4, "colors": colors,
                "ImageReader": ImageReader, "pdfmetrics": pdfmetrics}
    except Exception:
        return None


def _gc_pdf_safe_text(text: str) -> str:
    replacements = {
        "✓": "OK", "✗": "NICHT OK", "⚠": "WARNUNG",
        "•": "-", "→": "->", "≥": ">=", "≤": "<=", "═": "=", "─": "-",
        "–": "-", "—": "-",   # en dash, em dash → ASCII (ReportLab/Helvetica)
        "‘": "'", "’": "'",   # typogr. Apostrophe
        "“": '"', "”": '"',   # typogr. Anführungszeichen
    }
    safe = str(text or "")
    for old, new in replacements.items():
        safe = safe.replace(old, new)
    return safe


def _gc_parse_result_text(result_text: str) -> dict:
    info: dict = {
        "status": "unbekannt", "status_text": "Kein Status erkannt.",
        "own_parcel": "", "neighbor_count": "", "building_info": "",
        "method": "", "gross_setback": "", "small_setback": "",
        "main_side": "", "main_side_distance": "",
        "violations": [], "summary_lines": [], "warnings": [],
        # pro Nachbar: [{"name": str, "dist": float, "ok": bool, "is_main": bool}]
        "distances": [],
    }
    lines = [line.rstrip() for line in (result_text or "").splitlines()]
    summary_start = -1
    # Regex: "  ✓ Name  6.50 m" oder "  ✗ Name  2.30 m"
    dist_re = re.compile(r"^\s*[✓✗x]\s+(.+?)\s{2,}([\d.]+)\s*m\s*$")
    haupt_re = re.compile(r"HAUPTWOHNSEITE[:\s]+(.+?)\s{2,}([\d.]+)\s*m")
    main_name = ""
    for idx, line in enumerate(lines):
        stripped = line.strip()
        if "POSITIVE PRÜFUNG" in stripped:
            info["status"] = "positiv"; info["status_text"] = stripped
        elif "NEGATIVE PRÜFUNG" in stripped:
            info["status"] = "negativ"; info["status_text"] = stripped
        if stripped.startswith("Bauparzelle"):
            info["own_parcel"] = stripped.split(":", 1)[-1].strip()
        elif stripped.startswith("Nachbarparzellen"):
            info["neighbor_count"] = stripped.split(":", 1)[-1].strip()
        elif stripped.startswith("Gebäude"):
            info["building_info"] = stripped.split(":", 1)[-1].strip()
        elif stripped.startswith("Methode"):
            info["method"] = stripped.split(":", 1)[-1].strip()
        elif stripped.startswith("Grenzabstand groß"):
            info["gross_setback"] = stripped.split(":", 1)[-1].strip()
        elif "HAUPTWOHNSEITE" in stripped:
            hm = haupt_re.search(stripped)
            if hm:
                main_name = hm.group(1).strip()
                info["main_side"] = f"{main_name}  {hm.group(2)} m"
                info["main_side_distance"] = f"Abstand = {hm.group(2)} m"
            else:
                info["main_side"] = stripped.split(":", 1)[-1].strip()
        elif stripped.startswith("Abstand ="):
            info["main_side_distance"] = stripped
        if stripped.startswith("WARNUNG") or "⚠" in stripped:
            info["warnings"].append(stripped)
        if "ZUSAMMENFASSUNG" in stripped:
            summary_start = idx + 1
        # Distanz-Zeilen parsen (SCHRITT 1 + 2)
        dm = dist_re.match(line)
        if dm and "SCHRITT" not in stripped and "HAUPTWOHNSEITE" not in stripped:
            name = dm.group(1).strip()
            dist = float(dm.group(2))
            ok   = line.strip().startswith("✓")
            # Duplikate vermeiden (SCHRITT 1 + 2 listen gleiche Nachbarn)
            existing = next((r for r in info["distances"] if r["name"] == name), None)
            if existing is None:
                info["distances"].append({"name": name, "dist": dist, "ok": ok, "is_main": False})
            else:
                # Zweiter Eintrag = SCHRITT-2-Resultat (genauer), überschreiben
                existing["dist"] = dist
                existing["ok"]   = ok
    # Hauptwohnseite markieren
    if main_name:
        for row in info["distances"]:
            if row["name"] == main_name:
                row["is_main"] = True
    if summary_start >= 0:
        info["summary_lines"] = [l.strip() for l in lines[summary_start:] if l.strip()]
    violation_re = re.compile(r"^\s*(.+?)\s+\(([\d.]+)\s*m,\s*fehlt\s*([\d.]+)\s*m\)")
    for line in lines:
        m = violation_re.match(line)
        if m:
            info["violations"].append({
                "parcel": m.group(1).strip(),
                "distance_m": m.group(2),
                "missing_m": m.group(3),
            })
    return info


def _gc_has_swiss_context_terrain() -> bool:
    root_coll = bpy.data.collections.get(_SC_ROOT_COLL)
    if not root_coll:
        return False
    for sub in root_coll.children:
        if sub.name != _SC_TERRAIN_COLL:
            continue
        for obj in sub.objects:
            if obj.type == "MESH":
                return True
    return False


def _gc_first_view3d_context(context):
    area = getattr(context, "area", None)
    if area and area.type == "VIEW_3D":
        region = next((r for r in area.regions if r.type == "WINDOW"), None)
        space  = next((s for s in area.spaces  if s.type  == "VIEW_3D"), None)
        if region and space:
            return {"window": context.window, "area": area,
                    "region": region, "space": space}
    for window in context.window_manager.windows:
        for a in window.screen.areas:
            if a.type != "VIEW_3D":
                continue
            region = next((r for r in a.regions if r.type == "WINDOW"), None)
            space  = next((s for s in a.spaces  if s.type  == "VIEW_3D"), None)
            if region and space:
                return {"window": window, "area": a, "region": region, "space": space}
    return None


def _gc_ensure_visualization(context):
    props = context.scene.grenzcheck_props
    scene = context.scene
    own       = _gc_find_target_parcel(scene)
    neighbors = _gc_find_neighbors(scene)
    buildings = _gc_get_buildings(scene, props.collection_keyword)
    if not own or not neighbors or not buildings:
        return  # Kein Fehler – Screenshot trotzdem machen
    coll = _gc_vis_collection(scene)
    _gc_clear_vis(scene)
    screen = context.window.screen if context.window else None
    if screen:
        for a in screen.areas:
            if a.type == "VIEW_3D":
                for sp in a.spaces:
                    if sp.type == "VIEW_3D":
                        sp.shading.color_type = "OBJECT"
    p_mn, p_mx = _gc_bbox_world(own)
    z = p_mn.z + 0.05
    bldg_hull = _gc_building_hull(buildings, p_mn, p_mx)
    bm, bx    = _gc_combined_aabb_clipped(buildings, p_mn, p_mx)
    if bldg_hull:
        _gc_flat_polygon("_VIS_Gebäude", bldg_hull, z + 0.02, _COLOR_BUILDING, coll)
        raw = _gc_compute_grenzabstand(bldg_hull, own, neighbors)
    else:
        # Fallback: AABB-Rechteck als Gebäude-Footprint
        if bm and bx:
            rect = [Vector((bm.x, bm.y)), Vector((bx.x, bm.y)),
                    Vector((bx.x, bx.y)), Vector((bm.x, bx.y))]
            _gc_flat_polygon("_VIS_Gebäude", rect, z + 0.02, _COLOR_BUILDING, coll)
        raw = {nb: _gc_aabb_dist_xy(bm, bx, *_gc_bbox_world(nb)) for nb in neighbors}
    gdist   = {nb: (raw.get(nb) or 0.0) for nb in neighbors}
    ok_nb   = [nb for nb, d in gdist.items() if d >= props.grenzabstand_gross]
    haupt   = max(ok_nb, key=lambda nb: gdist[nb]) if ok_nb else None
    for nb in neighbors:
        color = (_COLOR_MAIN if nb is haupt
                 else _COLOR_VIOLATION if gdist[nb] < props.grenzabstand_klein
                 else _COLOR_OK)
        hull = _gc_parcel_hull_clipped(nb, p_mn, p_mx)
        name = f"_VIS_Parzelle_{nb.name[:26]}"
        if hull and len(hull) >= 3:
            _gc_flat_polygon(name, hull, z, color, coll)
        else:
            # Fallback: AABB-Rechteck der Nachbarparzelle
            nb_mn, nb_mx = _gc_bbox_world(nb)
            rect = [Vector((nb_mn.x, nb_mn.y)), Vector((nb_mx.x, nb_mn.y)),
                    Vector((nb_mx.x, nb_mx.y)), Vector((nb_mn.x, nb_mx.y))]
            _gc_flat_polygon(name, rect, z, color, coll)


def _gc_capture_viewport_png(context, output_path: Path) -> None:
    view_ctx = _gc_first_view3d_context(context)
    if not view_ctx:
        raise ParcelAddonError(
            "Keine VIEW_3D-Ansicht gefunden – PDF-Export benötigt einen offenen 3D-Viewport.")
    scene  = context.scene
    render = scene.render
    old_fp      = render.filepath
    old_use_ext = render.use_file_extension
    old_fmt     = render.image_settings.file_format
    old_color   = render.image_settings.color_mode
    output_path.parent.mkdir(parents=True, exist_ok=True)
    if output_path.exists():
        try: output_path.unlink()
        except OSError: pass
    try:
        render.filepath                   = str(output_path)
        render.use_file_extension         = False
        render.image_settings.file_format = "PNG"
        render.image_settings.color_mode  = "RGBA"
        override = {
            "window": view_ctx["window"],
            "screen": view_ctx["window"].screen,
            "area":   view_ctx["area"],
            "region": view_ctx["region"],
            "space_data": view_ctx["space"],
        }
        with context.temp_override(**override):
            bpy.ops.render.opengl(write_still=True, view_context=True)
    finally:
        render.filepath                   = old_fp
        render.use_file_extension         = old_use_ext
        render.image_settings.file_format = old_fmt
        render.image_settings.color_mode  = old_color
    if not output_path.exists() or output_path.stat().st_size == 0:
        raise ParcelAddonError("Viewport-Bild konnte nicht erzeugt werden.")


def _gc_resolve_report_root(scene) -> Path:
    props = scene.parcel_workflow
    candidates = []
    if props.project_root:
        candidates.append(Path(bpy.path.abspath(props.project_root)).expanduser())
    if props.resolved_project_root:
        candidates.append(Path(bpy.path.abspath(props.resolved_project_root)).expanduser())
    resolved = resolve_project_root(props.project_root)
    if resolved:
        candidates.append(resolved)
    for c in candidates:
        if looks_like_project_root(c):
            return c
    raise ParcelAddonError(
        "Projektordner konnte nicht bestimmt werden. "
        "Bitte im Add-on einen gültigen Projektordner setzen.")


def _gc_report_output_path(scene) -> Path:
    root = _gc_resolve_report_root(scene)
    egrid     = (scene.parcel_workflow.egrid or "").strip().upper() or "unbekannt"
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    reports_dir = root / "Protokolle" / "Grenzcheck-Berichte"
    reports_dir.mkdir(parents=True, exist_ok=True)
    return reports_dir / f"grenzcheck_{egrid}_{timestamp}.pdf"


def _gc_report_payload(scene, result_text: str) -> dict:
    props        = scene.grenzcheck_props
    parcel_props = scene.parcel_workflow
    parsed = _gc_parse_result_text(result_text)
    ifc_name = (Path(parcel_props.last_ifc_import).name
                if parcel_props.last_ifc_import else "unbekannt")
    metadata = [
        ("Datum",             datetime.now().strftime("%d.%m.%Y %H:%M:%S")),
        ("E-GRID",            (parcel_props.egrid or "").strip().upper() or "unbekannt"),
        ("Adresse",           parcel_props.adresse or ""),
        ("Gemeinde",          parcel_props.gemeinde or parcel_props.last_oereb_municipality or "unbekannt"),
        ("Nutzungszone",      parcel_props.last_nutzungszone or "unbekannt"),
        ("IFC-Datei",         ifc_name),
        ("IFC-Collection",    props.collection_keyword or "unbekannt"),
        ("Grenzabstand gross", f"{props.grenzabstand_gross:.2f} m"),
        ("Grenzabstand klein", f"{props.grenzabstand_klein:.2f} m"),
    ]
    terrain_note = ("" if _gc_has_swiss_context_terrain()
                    else "Hinweis: Keine Swiss-Context-Geländeumgebung geladen.")
    return {
        "parsed":       parsed,
        "metadata":     metadata,
        "terrain_note": terrain_note,
        "detail_lines": [_gc_pdf_safe_text(l) for l in (result_text or "").splitlines()],
    }


def _gc_pdf_escape(text: str) -> str:
    raw     = _gc_pdf_safe_text(text).encode("cp1252", "replace")
    escaped = []
    for value in raw:
        if value in (40, 41, 92):
            escaped.append(f"\\{chr(value)}")
        elif value < 32 or value > 126:
            escaped.append(f"\\{value:03o}")
        else:
            escaped.append(chr(value))
    return "".join(escaped)


class _GCSimplePdf:
    def __init__(self):
        self.objects: list = [None]
        self.page_objects: list = []
        self.pages_root = self.reserve()
        self.catalog    = self.reserve()
        self.font       = self.add(
            b"<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica "
            b"/Encoding /WinAnsiEncoding >>")

    def reserve(self) -> int:
        self.objects.append(None)
        return len(self.objects) - 1

    def add(self, payload: bytes) -> int:
        self.objects.append(payload)
        return len(self.objects) - 1

    def set(self, obj_id: int, payload: bytes) -> None:
        self.objects[obj_id] = payload

    def add_page(self, content: str, xobject_ref: int | None = None) -> None:
        resources = f"<< /Font << /F1 {self.font} 0 R >>".encode("ascii")
        if xobject_ref is not None:
            resources += f" /XObject << /Im1 {xobject_ref} 0 R >>".encode("ascii")
        resources += b" >>"
        stream      = content.encode("latin-1", "replace")
        content_obj = self.add(
            f"<< /Length {len(stream)} >>\nstream\n".encode("ascii")
            + stream + b"\nendstream")
        page_obj = self.add((
            f"<< /Type /Page /Parent {self.pages_root} 0 R /MediaBox [0 0 595 842] "
            f"/Resources {resources.decode('latin-1')} /Contents {content_obj} 0 R >>"
        ).encode("latin-1"))
        self.page_objects.append(page_obj)

    def finish(self) -> bytes:
        kids = " ".join(f"{p} 0 R" for p in self.page_objects)
        self.set(self.pages_root,
                 f"<< /Type /Pages /Count {len(self.page_objects)} /Kids [{kids}] >>".encode("ascii"))
        self.set(self.catalog,
                 f"<< /Type /Catalog /Pages {self.pages_root} 0 R >>".encode("ascii"))
        buf = bytearray(b"%PDF-1.4\n%\xe2\xe3\xcf\xd3\n")
        offsets = [0]
        for idx, payload in enumerate(self.objects[1:], start=1):
            if payload is None:
                raise RuntimeError(f"PDF object {idx} is empty.")
            offsets.append(len(buf))
            buf.extend(f"{idx} 0 obj\n".encode("ascii"))
            buf.extend(payload)
            buf.extend(b"\nendobj\n")
        startxref = len(buf)
        buf.extend(f"xref\n0 {len(self.objects)}\n".encode("ascii"))
        buf.extend(b"0000000000 65535 f \n")
        for offset in offsets[1:]:
            buf.extend(f"{offset:010d} 00000 n \n".encode("ascii"))
        buf.extend(
            f"trailer\n<< /Size {len(self.objects)} /Root {self.catalog} 0 R >>\n"
            f"startxref\n{startxref}\n%%EOF".encode("ascii"))
        return bytes(buf)


def _gc_pdf_text_block(lines: list, x: int, y: int,
                       font_size: int = 10, leading: int = 14) -> str:
    escaped = [_gc_pdf_escape(l) for l in lines]
    block   = [f"BT /F1 {font_size} Tf {leading} TL 1 0 0 1 {x} {y} Tm"]
    for idx, line in enumerate(escaped):
        block.append(f"({line}) Tj" if idx == 0 else f"T* ({line}) Tj")
    block.append("ET")
    return "\n".join(block)


def _gc_rotate_rgb_90cw(pixels, iw: int, ih: int):
    """Pixel-Array (RGBA flat) → RGB bytearray, 90° im Uhrzeigersinn gedreht.
    Gibt (rgb_bytes, new_width, new_height) zurück."""
    try:
        import numpy as np
        arr = np.array(pixels, dtype=np.float32).reshape(ih, iw, 4)
        rgb = np.clip(arr[:, :, :3] * 255, 0, 255).astype(np.uint8)
        rot = np.rot90(rgb, k=-1)          # k=-1 → 90° CW
        return bytearray(rot.tobytes()), rot.shape[1], rot.shape[0]
    except Exception:
        pass
    # Fallback: Pure-Python 90° CW (langsamer aber korrekt)
    new_w, new_h = ih, iw
    out = bytearray(new_w * new_h * 3)
    for ny in range(new_h):
        for nx in range(new_w):
            src_y = ih - 1 - nx
            src_x = ny
            src = (src_y * iw + src_x) * 4
            dst = (ny * new_w + nx) * 3
            out[dst]   = max(0, min(255, int(round(pixels[src]   * 255))))
            out[dst+1] = max(0, min(255, int(round(pixels[src+1] * 255))))
            out[dst+2] = max(0, min(255, int(round(pixels[src+2] * 255))))
    return out, new_w, new_h


def _gc_load_image_xobj(doc: "_GCSimplePdf", img_path) -> int | None:
    """Lädt ein PNG aus einem Pfad in ein PDF XObject. Gibt Objekt-ID oder None zurück."""
    if img_path is None:
        return None
    try:
        img = bpy.data.images.load(str(img_path), check_existing=False)
        try:
            iw, ih  = int(img.size[0]), int(img.size[1])
            pixels  = img.pixels[:]
        finally:
            bpy.data.images.remove(img)
        rgb = bytearray()
        for i in range(0, len(pixels), 4):
            rgb.append(max(0, min(255, int(round(pixels[i]   * 255)))))
            rgb.append(max(0, min(255, int(round(pixels[i+1] * 255)))))
            rgb.append(max(0, min(255, int(round(pixels[i+2] * 255)))))
        stream = zlib.compress(bytes(rgb))
        return doc.add((
            f"<< /Type /XObject /Subtype /Image /Width {iw} /Height {ih} "
            f"/ColorSpace /DeviceRGB /BitsPerComponent 8 /Filter /FlateDecode "
            f"/Length {len(stream)} >>\nstream\n"
        ).encode("ascii") + stream + b"\nendstream")
    except Exception as exc:
        print(f"  _gc_load_image_xobj: {exc}")
        return None


def _gc_egrid_from_name(name: str) -> str:
    """Extrahiert das EGRID (CH + 12 Ziffern) aus einem Blender-Objektnamen.

    Funktioniert auch wenn der Name durch _gc_short() abgeschnitten wurde, da
    die Suche kein Wortgrenzen-Anchor verwendet.

    Beispiel: "resf_CH354589007873_0001" → "CH354589007873"
    """
    m = re.search(r'CH\d{12}', name, re.IGNORECASE)
    return m.group(0).upper() if m else ""


def _gc_distance_label(row: dict) -> str:
    """Formatiert den Wert-Text einer Ergebniszeile.

    Zeigt: "4.33 m  |  Parzelle CH354589007873" (EGRID) oder
           "4.33 m  |  Parzelle <Kurzname>"  falls kein EGRID.
    Das 'name'-Feld enthält im Normalfall bereits das EGRID (gesetzt via _nb_lbl in _gc_run_check).
    Verwendet ASCII-Trennzeichen (|) damit alle PDF-Backends (builtin + ReportLab) korrekt rendern.
    """
    name = row["name"]
    # Wenn name bereits ein EGRID ist (beginnt mit CH + Ziffern) direkt verwenden
    if re.match(r'CH\d{9,12}', name, re.IGNORECASE):
        return f"{row['dist']:.2f} m  |  Parzelle {name.upper()}"
    # Sonst EGRID aus dem vollen Namen extrahieren
    egrid = _gc_egrid_from_name(name)
    ref   = egrid if egrid else name[:20]
    return f"{row['dist']:.2f} m  |  Parzelle {ref}"


def _gc_builtin_pdf_report(output_path: Path, report_data: dict) -> None:
    """Template-Layout: Titel · Info · Ergebnistabelle · 2×2 Kamera-Bilder."""
    doc    = _GCSimplePdf()
    parsed = report_data["parsed"]
    pos    = parsed["status"] == "positiv"
    meta   = dict(report_data["metadata"])
    slabel = "POSITIV" if pos else ("NEGATIV" if parsed["status"] == "negativ" else "Unbekannt")

    distances = parsed.get("distances", [])
    d_gross   = [r for r in distances if r["is_main"]]
    d_klein   = [r for r in distances if not r["is_main"]]
    # Fallback: wenn keine Hauptwohnseite markiert, grössten Abstand als Grosser GA nehmen
    if not d_gross and distances:
        best   = max(distances, key=lambda r: r["dist"])
        d_gross = [dict(best, is_main=True)]
        d_klein = [r for r in distances if r is not best]
    cam_imgs  = report_data.get("cam_images", {})
    try:
        g_gross_f = float(meta.get("Grenzabstand gross", "6.0 m").replace(" m", ""))
        g_klein_f = float(meta.get("Grenzabstand klein", "3.0 m").replace(" m", ""))
    except ValueError:
        g_gross_f, g_klein_f = 6.0, 3.0

    # Kamera-Bilder vorladen
    cam_xobjs = {k: _gc_load_image_xobj(doc, v) for k, v in cam_imgs.items()}

    # Farben
    CLR_GREEN  = "0.57 0.82 0.31 rg"   # #92D050
    CLR_YELLOW = "1.00 0.85 0.00 rg"   # #FFD900
    CLR_RED    = "0.80 0.10 0.10 rg"   # #CC1A1A
    CLR_GRAY   = "0.85 0.85 0.85 rg"   # #D9D9D9
    CLR_WHITE  = "1 1 1 rg"
    CLR_BLACK  = "0 0 0 rg"
    CLR_WHITE_TEXT = "q 1 1 1 rg"

    PW   = 595.0   # A4 Breite
    PH   = 842.0   # A4 Höhe
    ML   = 36.0    # linker Rand
    MR   = 36.0    # rechter Rand
    CW   = PW - ML - MR          # 523pt Content-Breite
    LC   = ML                    # linke Spalte x
    LCW  = CW * 0.38             # ~199pt (Label-Spalte)
    RC   = ML + LCW              # rechte Spalte x
    RCW  = CW - LCW              # ~324pt (Wert-Spalte)
    ROW_H = 18.0

    def rect(x, y, w, h, color_op):
        return f"q {color_op} {x:.1f} {y:.1f} {w:.1f} {h:.1f} re f Q"

    def cell_text(text, x, y, h, fs=9, bold=False):
        # _gc_pdf_text_block escapes internally – kein Vor-Escaping hier!
        return _gc_pdf_text_block([text], int(x + 3), int(y + h - fs - 2), fs, int(fs * 1.3))

    def hline(y, gray="0.75", lw=0.5):
        return f"{gray} g {lw} w {ML:.0f} {y:.1f} m {ML+CW:.0f} {y:.1f} l S 0 g 1 w"

    ops = []
    y   = PH - ML    # laufende y-Position (von oben nach unten)

    # ══ TITELZEILE ════════════════════════════════════════════════════════════
    th = 30.0
    y -= th
    title_clr = CLR_GREEN if pos else CLR_RED
    ops.append(rect(ML, y, CW, th, title_clr))
    ops += [CLR_WHITE_TEXT,
            _gc_pdf_text_block(["Grenzabstandcheck"],
                               int(ML + 6), int(y + th - 13 - 2), 13, 17),
            "Q"]
    y -= 4  # Abstand

    # ══ INFOTABELLE ═══════════════════════════════════════════════════════════
    info_rows = [
        ("EGRID NR",            meta.get("E-GRID", "")),
        ("Strasse + Ort",       meta.get("Adresse", "")),
        ("Gemeinde",            meta.get("Gemeinde", "")),
        ("Nutzungsplanzone",    meta.get("Nutzungszone", "")),
        ("Kleiner Grenzabstand",meta.get("Grenzabstand klein", "")),
        ("Grosser Grenzabstand",meta.get("Grenzabstand gross", "")),
    ]
    for lbl, val in info_rows:
        ops.append(rect(LC,      y - ROW_H, LCW, ROW_H, CLR_GRAY))
        ops.append(rect(RC,      y - ROW_H, RCW, ROW_H, CLR_WHITE))
        ops.append(hline(y - ROW_H, "0.70", 0.3))
        ops.append(cell_text(lbl, LC, y - ROW_H, ROW_H, 8))
        ops.append(cell_text(val, RC, y - ROW_H, ROW_H, 8))
        y -= ROW_H
    ops.append(hline(y, "0.50", 0.6))
    y -= 6

    # ══ ERGEBNISTABELLE ═══════════════════════════════════════════════════════
    result_rows = []
    for row in d_gross:
        ok    = row["dist"] >= g_gross_f
        label = "Grosser Grenzabstand"
        val   = _gc_distance_label(row)
        result_rows.append((label, val, ok, True))
    for row in d_klein:
        ok    = row["dist"] >= g_klein_f
        label = "Kleiner Grenzabstand"
        val   = _gc_distance_label(row)
        if not ok:
            viol = next((e for e in parsed["violations"] if row["name"] in e["parcel"]), None)
            if viol:
                val += f"  (fehlt {viol['missing_m']} m)"
        result_rows.append((label, val, ok, False))

    for lbl, val, ok, is_gross in result_rows:
        # Gross OK → gelb (schwarzer Text), Gross FAIL → rot (weisser Text)
        # Klein OK → grün (weisser Text),   Klein FAIL → rot (weisser Text)
        val_clr = (CLR_YELLOW if ok else CLR_RED) if is_gross else (CLR_GREEN if ok else CLR_RED)
        ops.append(rect(LC, y - ROW_H, LCW, ROW_H, CLR_GRAY))
        ops.append(rect(RC, y - ROW_H, RCW, ROW_H, val_clr))
        ops.append(hline(y - ROW_H, "0.70", 0.3))
        ops.append(cell_text(lbl, LC, y - ROW_H, ROW_H, 8))
        if is_gross and ok:
            # Gelber Hintergrund → schwarzer Text (kein white-Text-Wrapper)
            ops.append(cell_text(val, RC, y - ROW_H, ROW_H, 7.5))
        else:
            # Grüner/roter Hintergrund → weisser Text
            ops += [CLR_WHITE_TEXT, cell_text(val, RC, y - ROW_H, ROW_H, 7.5), "Q"]
        y -= ROW_H
    if not result_rows:
        ops.append(cell_text("(keine Ergebnisse)", LC, y - ROW_H, ROW_H, 8))
        y -= ROW_H
    ops.append(hline(y, "0.50", 0.6))
    y -= 8

    # ══ 2×2 FOTO-RASTER ═══════════════════════════════════════════════════════
    img_area_h = y - ML   # verbleibende Höhe
    cell_w = CW / 2.0
    cell_h = img_area_h / 2.0
    pad    = 4.0
    labels_order = [("nord","Bild Nord"),("ost","Bild Ost"),("sud","Bild Süd"),("west","Bild West")]

    # Zellen-Layout: [Nord Ost / Süd West]
    grid = [
        (labels_order[0], ML,           y - cell_h),
        (labels_order[1], ML + cell_w,  y - cell_h),
        (labels_order[2], ML,           ML),
        (labels_order[3], ML + cell_w,  ML),
    ]

    xobj_map: dict[str, int] = {}
    for (key, lbl), cx, cy in grid:
        xobj_id = cam_xobjs.get(key)
        # Rahmen
        ops.append(hline(cy + cell_h, "0.80", 0.4))
        # Label-Hintergrund
        ops.append(rect(cx + pad, cy + cell_h - 14, cell_w - 2*pad, 13, CLR_GRAY))
        ops.append(cell_text(lbl, cx + pad, cy + cell_h - 14, 13, 8))
        if xobj_id is not None:
            xobj_map[f"Im{xobj_id}"] = xobj_id
            avw = cell_w - 2 * pad
            avh = cell_h - 16 - pad
            # Bildgrösse anpassen (wir kennen dims nicht → nutze volle Fläche)
            ops.append(
                f"q {avw:.2f} 0 0 {avh:.2f} {cx+pad:.2f} {cy+pad:.2f} "
                f"cm /Im{xobj_id} Do Q")
        else:
            # Platzhalter
            ops.append(rect(cx + pad, cy + pad, cell_w - 2*pad, cell_h - 16 - pad, CLR_GRAY))
            ops.append(cell_text("(kein Bild)", cx + pad + 4, cy + pad, cell_h - 20, 8))

    # Senkrechte Mittellinie
    ops.append(f"0.75 g 0.4 w {ML+cell_w:.1f} {ML:.1f} m {ML+cell_w:.1f} {y:.1f} l S 0 g 1 w")

    # ══ SEITE HINZUFÜGEN ══════════════════════════════════════════════════════
    # Alle XObjects als Referenzen übergeben (via mehrfach xobject_ref nicht möglich →
    # wir modifizieren die Seitenressourcen direkt im page stream)
    page_stream = "\n".join(ops)
    # Ersten xobject_ref nehmen (damit _GCSimplePdf die /Resources anlegt), Rest manuell
    first_xobj = next(iter(xobj_map.values()), None)
    doc.add_page(page_stream, xobject_ref=first_xobj)

    # Restliche XObjects in die letzten Seiten-Resources eintragen
    if len(xobj_map) > 1 and doc.page_objects:
        pg_id  = doc.page_objects[-1]
        pg_raw = doc.objects[pg_id]
        if pg_raw:
            pg_str = pg_raw.decode("latin-1")
            xobj_entries = " ".join(
                f"/Im{xid} {xid} 0 R" for xid in xobj_map.values())
            pg_str = pg_str.replace(
                f"/Im{first_xobj} {first_xobj} 0 R",
                xobj_entries)
            doc.objects[pg_id] = pg_str.encode("latin-1")

    output_path.write_bytes(doc.finish())


def _gc_export_pdf_report(output_path: Path, report_data: dict) -> None:
    if ensure_reportlab() is not None:
        _gc_reportlab_pdf_report(output_path, report_data)
        return
    _gc_builtin_pdf_report(output_path, report_data)


def _gc_reportlab_pdf_report(output_path: Path, report_data: dict) -> None:
    """Template-Layout (ReportLab): Titel · Info · Ergebnistabelle · 2×2 Kamera-Bilder."""
    rl = ensure_reportlab()
    if rl is None:
        raise ParcelAddonError("ReportLab ist nicht verfügbar.")
    canvas_mod  = rl["canvas"]
    colors      = rl["colors"]
    A4          = rl["A4"]
    ImageReader = rl["ImageReader"]

    parsed  = report_data["parsed"]
    meta    = dict(report_data["metadata"])
    pos     = parsed["status"] == "positiv"
    cam_imgs = report_data.get("cam_images", {})

    c    = canvas_mod.Canvas(str(output_path), pagesize=A4)
    W, H = A4
    ML   = 36.0; MR = 36.0
    CW   = W - ML - MR
    LCW  = CW * 0.38
    RC   = ML + LCW
    RCW  = CW - LCW
    ROW_H = 18.0

    try:
        g_gross_f = float(meta.get("Grenzabstand gross", "6.0 m").replace(" m", ""))
        g_klein_f = float(meta.get("Grenzabstand klein", "3.0 m").replace(" m", ""))
    except ValueError:
        g_gross_f, g_klein_f = 6.0, 3.0

    distances = parsed.get("distances", [])
    d_gross   = [r for r in distances if r["is_main"]]
    d_klein   = [r for r in distances if not r["is_main"]]
    # Fallback: wenn keine Hauptwohnseite markiert, grössten Abstand als Grosser GA nehmen
    if not d_gross and distances:
        best   = max(distances, key=lambda r: r["dist"])
        d_gross = [dict(best, is_main=True)]
        d_klein = [r for r in distances if r is not best]

    GREEN  = colors.HexColor("#92D050")
    YELLOW = colors.HexColor("#FFD900")
    RED    = colors.HexColor("#CC1A1A")
    GRAY   = colors.HexColor("#D9D9D9")

    def draw_rect(x, y, w, h, fill_col):
        c.setFillColor(fill_col)
        c.rect(x, y, w, h, fill=1, stroke=0)
        c.setFillColor(colors.black)

    def draw_hline(y, col="#aaaaaa", lw=0.3):
        c.setStrokeColor(colors.HexColor(col))
        c.setLineWidth(lw)
        c.line(ML, y, ML + CW, y)
        c.setStrokeColor(colors.black); c.setLineWidth(1)

    def draw_cell(text, x, y, fs=8, col=None):
        c.setFont("Helvetica", fs)
        c.setFillColor(col if col else colors.black)
        c.drawString(x + 3, y + 4, _gc_pdf_safe_text(str(text)))
        c.setFillColor(colors.black)

    cur_y = H - ML

    # ── Titelzeile ────────────────────────────────────────────────────────────
    th = 30.0
    cur_y -= th
    draw_rect(ML, cur_y, CW, th, GREEN if pos else RED)
    c.setFillColor(colors.white)
    c.setFont("Helvetica-Bold", 13)
    c.drawString(ML + 6, cur_y + th - 13 - 4, "Grenzabstandcheck")
    c.setFillColor(colors.black)
    cur_y -= 4

    # ── Infotabelle ───────────────────────────────────────────────────────────
    info_rows = [
        ("EGRID NR",             meta.get("E-GRID", "")),
        ("Strasse + Ort",        meta.get("Adresse", "")),
        ("Gemeinde",             meta.get("Gemeinde", "")),
        ("Nutzungsplanzone",     meta.get("Nutzungszone", "")),
        ("Kleiner Grenzabstand", meta.get("Grenzabstand klein", "")),
        ("Grosser Grenzabstand", meta.get("Grenzabstand gross", "")),
    ]
    for lbl, val in info_rows:
        ry = cur_y - ROW_H
        draw_rect(ML, ry, LCW, ROW_H, GRAY)
        draw_rect(RC, ry, RCW, ROW_H, colors.white)
        draw_hline(ry, "#bbbbbb", 0.25)
        draw_cell(lbl, ML, ry, 8)
        draw_cell(val, RC, ry, 8)
        cur_y -= ROW_H
    draw_hline(cur_y, "#888888", 0.5)
    cur_y -= 6

    # ── Ergebnistabelle ───────────────────────────────────────────────────────
    result_rows = []
    for row in d_gross:
        ok    = row["dist"] >= g_gross_f
        label = "Grosser Grenzabstand"
        val   = _gc_distance_label(row)
        result_rows.append((label, val, ok, True))
    for row in d_klein:
        ok    = row["dist"] >= g_klein_f
        label = "Kleiner Grenzabstand"
        val   = _gc_distance_label(row)
        if not ok:
            viol = next((e for e in parsed["violations"] if row["name"] in e["parcel"]), None)
            if viol:
                val += f"  (fehlt {viol['missing_m']} m)"
        result_rows.append((label, val, ok, False))

    if not result_rows:
        c.setFont("Helvetica-Oblique", 8); c.setFillColor(colors.HexColor("#888888"))
        c.drawString(ML + 3, cur_y - ROW_H + 4, "(keine Ergebnisse)")
        c.setFillColor(colors.black)
        cur_y -= ROW_H
    else:
        for lbl, val, ok, is_gross in result_rows:
            ry = cur_y - ROW_H
            # Gross OK → gelb (schwarzer Text), Gross FAIL → rot (weisser Text)
            # Klein OK → grün (weisser Text),   Klein FAIL → rot (weisser Text)
            val_col = (YELLOW if ok else RED) if is_gross else (GREEN if ok else RED)
            txt_col = colors.black if (is_gross and ok) else colors.white
            draw_rect(ML, ry, LCW, ROW_H, GRAY)
            draw_rect(RC, ry, RCW, ROW_H, val_col)
            draw_hline(ry, "#bbbbbb", 0.25)
            draw_cell(lbl, ML, ry, 8)
            draw_cell(val, RC, ry, 7.5, txt_col)
            cur_y -= ROW_H
    draw_hline(cur_y, "#888888", 0.5)
    cur_y -= 8

    # ── 2×2 Foto-Raster ───────────────────────────────────────────────────────
    img_area_h = cur_y - ML
    cell_w  = CW / 2.0
    cell_h  = img_area_h / 2.0
    pad     = 4.0
    label_h = 14.0

    grid_order = [
        ("nord", "Bild Nord",  ML,           cur_y - cell_h),
        ("ost",  "Bild Ost",   ML + cell_w,  cur_y - cell_h),
        ("sud",  "Bild Sued",  ML,           ML),
        ("west", "Bild West",  ML + cell_w,  ML),
    ]
    for key, lbl, cx, cy in grid_order:
        # Label-Zeile
        draw_rect(cx + pad, cy + cell_h - label_h, cell_w - 2*pad, label_h, GRAY)
        c.setFont("Helvetica", 8); c.setFillColor(colors.black)
        c.drawString(cx + pad + 3, cy + cell_h - label_h + 4, lbl)
        # Bild
        img_path = cam_imgs.get(key)
        if img_path and Path(img_path).exists():
            try:
                ir = ImageReader(str(img_path))
                iw, ih = ir.getSize()
                avw = cell_w - 2*pad
                avh = cell_h - label_h - pad
                scale = min(avw / max(iw, 1), avh / max(ih, 1))
                dw = iw * scale; dh = ih * scale
                ix = cx + pad + (avw - dw) / 2.0
                iy = cy + pad + (avh - dh) / 2.0
                c.drawImage(ir, ix, iy, width=dw, height=dh,
                            preserveAspectRatio=False)
            except Exception:
                draw_rect(cx+pad, cy+pad, cell_w-2*pad, cell_h-label_h-pad, GRAY)
        else:
            draw_rect(cx+pad, cy+pad, cell_w-2*pad, cell_h-label_h-pad, GRAY)
            c.setFont("Helvetica-Oblique", 8); c.setFillColor(colors.HexColor("#888888"))
            c.drawString(cx+pad+4, cy+pad+4, "(kein Bild)")
            c.setFillColor(colors.black)

    # Trennlinien Raster
    c.setStrokeColor(colors.HexColor("#bbbbbb")); c.setLineWidth(0.4)
    c.line(ML + cell_w, ML, ML + cell_w, cur_y)
    c.line(ML, ML + cell_h, ML + CW, ML + cell_h)
    c.setStrokeColor(colors.black); c.setLineWidth(1)

    c.save()


# ── Operator: PDF exportieren ─────────────────────────────────────────────────

_GC_CAM_NAMES = {
    "nord": "_GC_Cam_Nord",
    "ost":  "_GC_Cam_Ost",
    "sud":  "_GC_Cam_Süd",
    "west": "_GC_Cam_West",
}
_GC_CAMERAS_COLL = "_GC_Kameras"


class GRENZCHECK_OT_create_cameras(Operator):
    bl_idname     = "parcel_workflow.grenzcheck_create_cameras"
    bl_label      = "4 Kameras erstellen"
    bl_description = "Erstellt 4 Perspektiv-Kameras (Nord/Ost/Süd/West, 45°) für den PDF-Bericht"

    def execute(self, context):
        scene  = context.scene
        props  = scene.grenzcheck_props
        own    = _gc_find_target_parcel(scene)
        if not own:
            self.report({'WARNING'}, "Keine Bauparzelle gefunden.")
            return {'CANCELLED'}

        p_mn, p_mx = _gc_bbox_world(own)
        cx = (p_mn.x + p_mx.x) / 2.0
        cy = (p_mn.y + p_mx.y) / 2.0
        cz = p_mn.z

        # Abstand: 2× grösste Parzellenausdehnung, Höhe = Abstand → 45°
        dist = max(p_mx.x - p_mn.x, p_mx.y - p_mn.y) * 2.0
        ht   = dist  # 45° Elevation: vertical = horizontal

        # Collection anlegen
        coll = bpy.data.collections.get(_GC_CAMERAS_COLL)
        if coll is None:
            coll = bpy.data.collections.new(_GC_CAMERAS_COLL)
            scene.collection.children.link(coll)

        directions = [
            ("nord", Vector((cx,        cy - dist, cz + ht))),
            ("ost",  Vector((cx + dist, cy,        cz + ht))),
            ("sud",  Vector((cx,        cy + dist, cz + ht))),
            ("west", Vector((cx - dist, cy,        cz + ht))),
        ]
        target = Vector((cx, cy, cz))

        for key, pos in directions:
            cam_name = _GC_CAM_NAMES[key]
            # Altes Objekt entfernen
            old = bpy.data.objects.get(cam_name)
            if old:
                for c in list(bpy.data.collections) + [scene.collection]:
                    if old.name in c.objects:
                        c.objects.unlink(old)
                bpy.data.objects.remove(old, do_unlink=True)
            # Kamera-Daten
            cam_data = bpy.data.cameras.new(cam_name)
            cam_data.type  = 'PERSP'
            cam_data.lens  = 28          # Weitwinkel für guten Überblick
            cam_data.clip_end = 10000.0
            # Objekt
            cam_obj          = bpy.data.objects.new(cam_name, cam_data)
            cam_obj.location = pos
            direction        = target - pos
            cam_obj.rotation_euler = direction.to_track_quat('-Z', 'Y').to_euler()
            coll.objects.link(cam_obj)

        self.report({'INFO'}, "4 Kameras erstellt: Nord / Ost / Süd / West")
        return {'FINISHED'}


def _gc_render_camera_png(context, cam_name: str, output_path: Path) -> bool:
    """Rendert eine Kamera mit bpy.ops.render.render() als PNG. Gibt True bei Erfolg zurück."""
    cam_obj = bpy.data.objects.get(cam_name)
    if not cam_obj or cam_obj.type != 'CAMERA':
        return False
    scene = context.scene
    old_cam    = scene.camera
    old_fp     = scene.render.filepath
    old_fmt    = scene.render.image_settings.file_format
    old_res_x  = scene.render.resolution_x
    old_res_y  = scene.render.resolution_y
    old_pct    = scene.render.resolution_percentage
    output_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        scene.camera = cam_obj
        scene.render.filepath               = str(output_path.with_suffix(""))
        scene.render.image_settings.file_format = "PNG"
        scene.render.resolution_x           = 960
        scene.render.resolution_y           = 720
        scene.render.resolution_percentage  = 100
        bpy.ops.render.render(write_still=True)
        return output_path.exists()
    except Exception as exc:
        print(f"  _gc_render_camera_png({cam_name}): {exc}")
        return False
    finally:
        scene.camera                        = old_cam
        scene.render.filepath               = old_fp
        scene.render.image_settings.file_format = old_fmt
        scene.render.resolution_x           = old_res_x
        scene.render.resolution_y           = old_res_y
        scene.render.resolution_percentage  = old_pct


class GRENZCHECK_OT_export_pdf(Operator):
    bl_idname     = "parcel_workflow.grenzcheck_export_pdf"
    bl_label      = "PDF exportieren"
    bl_description = "Exportiert den letzten Grenzcheck als PDF-Bericht und öffnet ihn im Browser"

    def execute(self, context):
        props = context.scene.grenzcheck_props
        if not props.result_text:
            props.pdf_status = "Kein Prüfergebnis vorhanden."
            self.report({"WARNING"}, "Bitte zuerst 'Grenzabstand prüfen' ausführen.")
            return {"CANCELLED"}

        try:
            output_path = _gc_report_output_path(context.scene)
            report_data = _gc_report_payload(context.scene, props.result_text)
            _gc_ensure_visualization(context)

            tmp_dir = Path(tempfile.mkdtemp(prefix="gc_pdf_"))
            try:
                # 4 Kamera-Renderings
                cam_images: dict[str, Path | None] = {}
                for key, cam_name in _GC_CAM_NAMES.items():
                    cam_path = tmp_dir / f"cam_{key}.png"
                    ok = _gc_render_camera_png(context, cam_name, cam_path)
                    cam_images[key] = cam_path if ok else None

                report_data["cam_images"] = cam_images
                _gc_export_pdf_report(output_path, report_data)
            finally:
                import shutil as _shutil
                try: _shutil.rmtree(tmp_dir, ignore_errors=True)
                except Exception: pass

        except ParcelAddonError as exc:
            props.pdf_status = str(exc)
            self.report({"ERROR"}, str(exc))
            return {"CANCELLED"}
        except Exception as exc:
            props.pdf_status = f"PDF-Export fehlgeschlagen: {exc}"
            self.report({"ERROR"}, props.pdf_status)
            return {"CANCELLED"}

        props.last_pdf_path = str(output_path)
        props.pdf_status    = f"PDF exportiert: {output_path.name}"
        self.report({"INFO"}, props.pdf_status)
        webbrowser.open(output_path.as_uri())
        return {"FINISHED"}


# ── Ende Grenzcheck-Block ─────────────────────────────────────────────────────


# ══════════════════════════════════════════════════════════════════════════════
# SWISS CONTEXT IMPORTER  (_sc_ Prefix)
# Portiert von CodeKay/swiss_context_importer_E-Grid.py
# Datenabfrage läuft im Hintergrund-Thread; Blender-Objekte werden im Main-Thread erstellt.
# ══════════════════════════════════════════════════════════════════════════════

_SC_SCENE_CRS          = "EPSG:2056"
_SC_ROOT_COLL          = "Swiss_Context_LV95"
_SC_TERRAIN_COLL       = "Terrain"
_SC_BUILDINGS_COLL     = "Buildings"
_SC_ROADS_COLL         = "Roads"
_SC_PARCEL_COLL        = "Parcel"
_SC_HADR_COLL          = "HADR"
_SC_ROAD_Z_OFFSET      = 0.05
_SC_PARCEL_Z_OFFSET    = 0.08
_SC_DEFAULT_BLD_H      = 9.0
_SC_DEFAULT_LEVEL_H    = 3.0
_SC_TERRAIN_MARGIN_M   = 30.0
_SC_GEOADMIN_SEARCH    = "https://api3.geo.admin.ch/rest/services/ech/SearchServer"
_SC_GEOADMIN_FIND      = "https://api3.geo.admin.ch/rest/services/ech/MapServer/find"
_SC_GEOADMIN_PROFILE   = "https://api3.geo.admin.ch/rest/services/profile.json"
_SC_REFRAME_URL        = "https://geodesy.geo.admin.ch/reframe/wgs84tolv95"
_SC_OVERPASS_URL       = "https://overpass.osm.ch/api/interpreter"
_SC_HTTP_TIMEOUT       = 120
_SC_HTTP_TIMEOUT_OP    = 180
_SC_HTTP_RETRIES       = 3
_SC_HTTP_RETRY_DELAY   = 2.0
_SC_UA                 = "Blender-LV95-Context-Importer/2.0"

try:
    _SC_TRANSFORMER = Transformer.from_crs("EPSG:4326", "EPSG:2056", always_xy=True) if Transformer else None
except Exception:
    _SC_TRANSFORMER = None


# ── HTTP ──────────────────────────────────────────────────────────────────────

def _sc_http_get_json(url, params=None, timeout=_SC_HTTP_TIMEOUT):
    if params:
        url = f"{url}?{urllib.parse.urlencode(params)}"
    req = urllib.request.Request(url, headers={"User-Agent": _SC_UA, "Accept": "application/json"})
    last_err = None
    for attempt in range(1, _SC_HTTP_RETRIES + 1):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return json.loads(r.read().decode("utf-8"))
        except Exception as exc:
            last_err = exc
            if attempt < _SC_HTTP_RETRIES:
                time.sleep(_SC_HTTP_RETRY_DELAY)
    raise RuntimeError(f"HTTP GET failed after {_SC_HTTP_RETRIES} attempts: {last_err}\nURL: {url}")


def _sc_http_post_json(url, body_text, timeout=_SC_HTTP_TIMEOUT_OP):
    req = urllib.request.Request(
        url, data=body_text.encode("utf-8"),
        headers={"User-Agent": _SC_UA, "Content-Type": "text/plain; charset=utf-8", "Accept": "application/json"},
    )
    last_err = None
    for attempt in range(1, _SC_HTTP_RETRIES + 1):
        try:
            with urllib.request.urlopen(req, timeout=timeout) as r:
                return json.loads(r.read().decode("utf-8"))
        except Exception as exc:
            last_err = exc
            if attempt < _SC_HTTP_RETRIES:
                time.sleep(_SC_HTTP_RETRY_DELAY)
    raise RuntimeError(f"HTTP POST failed after {_SC_HTTP_RETRIES} attempts: {last_err}\nURL: {url}")


# ── Koordinaten ───────────────────────────────────────────────────────────────

def _sc_wgs84_to_lv95_approx(lon, lat):
    lat_aux = (lat * 3600.0 - 169028.66) / 10000.0
    lon_aux = (lon * 3600.0 - 26782.5) / 10000.0
    e = (2600072.37 + 211455.93 * lon_aux - 10938.51 * lon_aux * lat_aux
         - 0.36 * lon_aux * lat_aux ** 2 - 44.54 * lon_aux ** 3)
    n = (1200147.07 + 308807.95 * lat_aux + 3745.25 * lon_aux ** 2
         + 76.63 * lat_aux ** 2 - 194.56 * lon_aux ** 2 * lat_aux + 119.79 * lat_aux ** 3)
    return e, n


def _sc_lv95_to_wgs84_approx(e, n):
    e_aux = (e - 2600000.0) / 1000000.0
    n_aux = (n - 1200000.0) / 1000000.0
    lon = (2.6779094 + 4.728982 * e_aux + 0.791484 * e_aux * n_aux
           + 0.1306 * e_aux * n_aux ** 2 - 0.0436 * e_aux ** 3) * 100.0 / 36.0
    lat = (16.9023892 + 3.238272 * n_aux - 0.270978 * e_aux ** 2
           - 0.002528 * n_aux ** 2 - 0.0447 * e_aux ** 2 * n_aux - 0.0140 * n_aux ** 3) * 100.0 / 36.0
    return lon, lat


def _sc_wgs84_to_lv95(lon, lat):
    if _SC_TRANSFORMER is not None:
        return tuple(float(v) for v in _SC_TRANSFORMER.transform(lon, lat))
    return _sc_wgs84_to_lv95_approx(lon, lat)


def _sc_lv95_to_local_xy(e, n, origin_e, origin_n):
    return e - origin_e, n - origin_n


def _sc_lonlat_to_local_xy(lon, lat, origin_e, origin_n):
    e, n = _sc_wgs84_to_lv95(lon, lat)
    return e - origin_e, n - origin_n


# ── Geometrie-Hilfsfunktionen ─────────────────────────────────────────────────

def _sc_clean_ring_xy(points_xy, tol=1e-6):
    cleaned = []
    for pt in points_xy:
        if not cleaned or abs(pt[0]-cleaned[-1][0]) > tol or abs(pt[1]-cleaned[-1][1]) > tol:
            cleaned.append(pt)
    if len(cleaned) > 1:
        f, l = cleaned[0], cleaned[-1]
        if abs(f[0]-l[0]) < tol and abs(f[1]-l[1]) < tol:
            cleaned.pop()
    return cleaned


def _sc_normalize2d(x, y):
    length = math.hypot(x, y)
    return (x / length, y / length) if length > 1e-9 else (1.0, 0.0)


def _sc_lv95_centroid(points_lv95):
    return sum(p[0] for p in points_lv95) / len(points_lv95), sum(p[1] for p in points_lv95) / len(points_lv95)


def _sc_bbox_from_lv95(points_lv95, margin_m=0.5):
    return (min(p[0] for p in points_lv95) - margin_m, min(p[1] for p in points_lv95) - margin_m,
            max(p[0] for p in points_lv95) + margin_m, max(p[1] for p in points_lv95) + margin_m)


def _sc_point_on_seg(px, py, ax, ay, bx, by, tol=1e-6):
    cross = (px-ax)*(by-ay) - (py-ay)*(bx-ax)
    if abs(cross) > tol:
        return False
    dot = (px-ax)*(bx-ax) + (py-ay)*(by-ay)
    seg_sq = (bx-ax)**2 + (by-ay)**2
    return -tol <= dot <= seg_sq + tol


def _sc_point_in_poly(px, py, poly_xy, tol=1e-6):
    poly_xy = _sc_clean_ring_xy(poly_xy, tol)
    n = len(poly_xy)
    if n < 3:
        return False
    inside = False
    for i in range(n):
        x1, y1 = poly_xy[i]
        x2, y2 = poly_xy[(i+1) % n]
        if _sc_point_on_seg(px, py, x1, y1, x2, y2, tol):
            return True
        if (y1 > py) != (y2 > py):
            xc = x1 + (py-y1)*(x2-x1)/(y2-y1)
            if xc >= px - tol:
                inside = not inside
    return inside


def _sc_dist_sq(a, b):
    return (a[0]-b[0])**2 + (a[1]-b[1])**2


# ── Parzelle / HADR ───────────────────────────────────────────────────────────

def _sc_get_parcel_centroid(egrid):
    """Gibt (lat, lon, label) des Parzellenzentroids zurück."""
    data = _sc_http_get_json(_SC_GEOADMIN_SEARCH, params={
        "searchText": egrid, "type": "locations", "origins": "parcel",
        "limit": 10, "sr": 4326, "lang": "de",
    })
    results = data.get("results", [])
    if not results:
        raise RuntimeError(f"Keine Parzelle für EGRID '{egrid}' gefunden.")
    exact = [r for r in results if r.get("attrs", {}).get("featureId", "").upper() == egrid]
    best = exact[0] if exact else results[0]
    attrs = best.get("attrs", {})
    label = re.sub(r"<[^>]+>", "", attrs.get("label", "") or "").strip() or egrid
    return float(attrs["lat"]), float(attrs["lon"]), label


def _sc_get_parcel_polygon(egrid):
    """Gibt Parzellenpolygon als [(E, N), ...] in LV95 zurück oder None."""
    data = _sc_http_get_json(_SC_GEOADMIN_FIND, params={
        "layer": "ch.kantone.cadastralwebmap-farbe", "searchField": "egris_egrid",
        "searchText": egrid, "returnGeometry": "true", "sr": 2056, "geometryFormat": "esrijson",
    })
    results = data.get("results", [])
    if not results:
        return None
    rings = results[0].get("geometry", {}).get("rings", [])
    if not rings:
        return None
    return _sc_clean_ring_xy([(float(p[0]), float(p[1])) for p in rings[0]], tol=0.01)


def _sc_get_hadr_point(parcel_polygon_lv95):
    """Sucht HADR-Adresspunkt innerhalb der Parzelle via GeoAdmin SearchServer."""
    min_e, min_n, max_e, max_n = _sc_bbox_from_lv95(parcel_polygon_lv95, margin_m=1.0)
    data = _sc_http_get_json(_SC_GEOADMIN_SEARCH, params={
        "bbox": f"{min_e:.3f},{min_n:.3f},{max_e:.3f},{max_n:.3f}",
        "type": "locations", "origins": "address", "limit": 50, "sr": 2056, "lang": "de",
    })
    results = data.get("results", [])
    if not results:
        return None
    parcel_center = _sc_lv95_centroid(parcel_polygon_lv95)
    candidates = []
    for r in results:
        attrs = r.get("attrs", {})
        lat, lon = attrs.get("lat"), attrs.get("lon")
        if lat is None or lon is None:
            continue
        try:
            pt = _sc_wgs84_to_lv95(float(lon), float(lat))
        except Exception:
            continue
        if not _sc_point_in_poly(pt[0], pt[1], parcel_polygon_lv95, tol=0.2):
            continue
        label = re.sub(r"<[^>]+>", "", attrs.get("label", "") or "").strip()
        candidates.append({
            "point_lv95": pt,
            "street_name": label,
            "house_number": "",
            "gwr_egid": str(attrs.get("featureId") or r.get("id") or ""),
            "source_path": "",
            "source_api": "GeoAdmin SearchServer",
            "source_href": "",
            "source_layer_title": "address",
            "distance_sq": _sc_dist_sq(pt, parcel_center),
        })
    if not candidates:
        return None
    candidates.sort(key=lambda x: x["distance_sq"])
    return candidates[0]


# ── Terrain ───────────────────────────────────────────────────────────────────

class _ScTerrainSampler:
    def __init__(self, x_min, y_min, step, cols, rows, heights):
        self.x_min, self.y_min, self.step = x_min, y_min, step
        self.cols, self.rows, self.heights = cols, rows, heights
        self.z_offset = 0.0

    def _raw(self, x, y):
        gx = max(0.0, min((x - self.x_min) / self.step, self.cols - 1.0))
        gy = max(0.0, min((y - self.y_min) / self.step, self.rows - 1.0))
        ix = min(int(math.floor(gx)), self.cols - 2)
        iy = min(int(math.floor(gy)), self.rows - 2)
        tx, ty = gx - ix, gy - iy
        z00 = self.heights[iy][ix];     z10 = self.heights[iy][ix+1]
        z01 = self.heights[iy+1][ix];   z11 = self.heights[iy+1][ix+1]
        return (z00*(1-tx)+z10*tx)*(1-ty) + (z01*(1-tx)+z11*tx)*ty

    def sample_absolute(self, x, y):
        return self._raw(x, y)

    def sample(self, x, y):
        return self._raw(x, y) - self.z_offset

    def set_z_offset(self, z):
        self.z_offset = float(z)


def _sc_fetch_profile_row(x0_abs, y_abs, x1_abs, nb_points):
    geom = {"type": "LineString", "coordinates": [[x0_abs, y_abs], [x1_abs, y_abs]]}
    return _sc_http_get_json(_SC_GEOADMIN_PROFILE, params={
        "geom": json.dumps(geom, separators=(",", ":")),
        "sr": 2056, "nb_points": max(nb_points, 50), "distinct_points": "True",
    })


def _sc_pick_profile_height(entry):
    alts = entry.get("alts", {})
    for key in ("DTM2", "COMB", "DTM25"):
        v = alts.get(key)
        if v is not None:
            return float(v)
    raise RuntimeError(f"Kein Höhenkanal: {entry}")


def _sc_sample_at_dist(profile, target_dist):
    if not profile:
        raise RuntimeError("Leeres Profil")
    if target_dist <= profile[0]["dist"]:
        return _sc_pick_profile_height(profile[0])
    if target_dist >= profile[-1]["dist"]:
        return _sc_pick_profile_height(profile[-1])
    for p0, p1 in zip(profile, profile[1:]):
        d0, d1 = float(p0["dist"]), float(p1["dist"])
        if d0 <= target_dist <= d1:
            t = (target_dist - d0) / (d1 - d0) if abs(d1 - d0) > 1e-9 else 0.0
            return _sc_pick_profile_height(p0) * (1 - t) + _sc_pick_profile_height(p1) * t
    return _sc_pick_profile_height(profile[-1])


def _sc_fetch_terrain_heights(origin_e, origin_n, radius_m, step_m, progress_cb=None):
    """Thread-sicher: lädt Geländehöhen von swisstopo. Gibt dict zurück."""
    half = radius_m + _SC_TERRAIN_MARGIN_M
    x_min, x_max, y_min, y_max = -half, half, -half, half
    cols = int(round((x_max - x_min) / step_m)) + 1
    rows = int(round((y_max - y_min) / step_m)) + 1
    heights = []
    for row_idx in range(rows):
        y_abs = origin_n + y_min + row_idx * step_m
        profile = _sc_fetch_profile_row(origin_e + x_min, y_abs, origin_e + x_max, cols)
        total_d = float(profile[-1]["dist"]) if profile else (x_max - x_min)
        heights.append([
            _sc_sample_at_dist(profile, total_d * (col / (cols - 1)) if cols > 1 else 0.0)
            for col in range(cols)
        ])
        if progress_cb:
            progress_cb(f"Terrain Zeile {row_idx+1}/{rows}")
    return {"x_min": x_min, "y_min": y_min, "step": step_m, "cols": cols, "rows": rows, "heights": heights}


# ── OSM ───────────────────────────────────────────────────────────────────────

def _sc_fetch_osm_data(lat, lon, radius_m):
    query = (
        f"[out:json][timeout:120];\n(\n"
        f"  way[\"building\"](around:{radius_m},{lat},{lon});\n"
        f"  relation[\"building\"](around:{radius_m},{lat},{lon});\n"
        f"  way[\"highway\"][\"highway\"!~\"footway|path|cycleway|steps|corridor|"
        f"bridleway|proposed|construction|raceway|elevator|platform|track\"]"
        f"(around:{radius_m},{lat},{lon});\n);\nout body geom;\n"
    )
    data = _sc_http_post_json(_SC_OVERPASS_URL, query)
    elements = data.get("elements", [])
    buildings = [e for e in elements if "building" in e.get("tags", {})]
    roads = [e for e in elements if "highway" in e.get("tags", {}) and "building" not in e.get("tags", {})]
    return buildings, roads


# ── Kartenlayer (swisstopo WMTS) ──────────────────────────────────────────────

_SC_SAT_LAYER = "ch.swisstopo.swissimage"          # Luftbild
_SC_MAP_LAYER = "ch.swisstopo.pixelkarte-farbe"    # Topografische Landeskarte (wie screenshot)
_SC_SAT_ZOOM  = 18          # ~0.6 m/Pixel in der Schweiz


def _sc_deg2tile(lat_deg, lon_deg, zoom):
    """WGS84 → WebMercator-Kachel (x, y)."""
    n = 1 << zoom
    x = int((lon_deg + 180.0) / 360.0 * n)
    lat_r = math.radians(lat_deg)
    y = int((1.0 - math.asinh(math.tan(lat_r)) / math.pi) / 2.0 * n)
    return x, y


def _sc_tile_nw(x, y, zoom):
    """Nord-West-Ecke (lat, lon) einer Kachel (x, y) bei gegebenem Zoom."""
    n = 1 << zoom
    lon = x / n * 360.0 - 180.0
    lat = math.degrees(math.atan(math.sinh(math.pi * (1 - 2 * y / n))))
    return lat, lon


def _sc_fetch_sat_tile_bytes(z, x, y, layer=None):
    """Lädt eine WMTS-Kachel (Satellit oder Landeskarte)."""
    if layer is None:
        layer = _SC_SAT_LAYER
    url = (f"https://wmts.geo.admin.ch/1.0.0/{layer}"
           f"/default/current/3857/{z}/{x}/{y}.jpeg")
    req = urllib.request.Request(url, headers={"User-Agent": _SC_UA})
    with urllib.request.urlopen(req, timeout=30) as r:
        return r.read()


def _sc_fetch_all_tiles(center_lat, center_lon, half_m, zoom=_SC_SAT_ZOOM, progress_cb=None, layer=None):
    """Lädt alle WMTS-Kacheln für das Gebiet. Gibt Tile-Daten + Bounding-Box zurück."""
    lat_per_m = 1.0 / 111320.0
    lon_per_m = 1.0 / max(111320.0 * math.cos(math.radians(center_lat)), 1.0)
    lat_d = half_m * lat_per_m
    lon_d = half_m * lon_per_m

    # NW-Ecke: max_lat / min_lon; SE-Ecke: min_lat / max_lon
    x_nw, y_nw = _sc_deg2tile(center_lat + lat_d, center_lon - lon_d, zoom)
    x_se, y_se = _sc_deg2tile(center_lat - lat_d, center_lon + lon_d, zoom)
    x_min, x_max = min(x_nw, x_se), max(x_nw, x_se)
    y_min, y_max = min(y_nw, y_se), max(y_nw, y_se)  # y_min = nördlichste Kachel

    n_tiles = (x_max - x_min + 1) * (y_max - y_min + 1)
    layer = layer or _SC_SAT_LAYER
    layer_label = "Landeskarte" if "pixelkarte" in layer else "Satellitenbild"
    if progress_cb:
        progress_cb(f"[4/5] {layer_label}-Kacheln ({n_tiles} Stück)...")

    tiles = []
    for ty in range(y_min, y_max + 1):
        for tx in range(x_min, x_max + 1):
            try:
                raw = _sc_fetch_sat_tile_bytes(zoom, tx, ty, layer=layer)
                tiles.append((tx, ty, raw))
            except Exception as exc:
                print(f"  Kachel {tx}/{ty} nicht geladen: {exc}")
                tiles.append((tx, ty, None))

    nw_lat, nw_lon = _sc_tile_nw(x_min, y_min, zoom)
    se_lat, se_lon = _sc_tile_nw(x_max + 1, y_max + 1, zoom)
    return {
        "tiles": tiles,
        "x_min": x_min, "y_min": y_min,
        "x_max": x_max, "y_max": y_max,
        "zoom": zoom,
        "lat_north": nw_lat, "lat_south": se_lat,
        "lon_west":  nw_lon, "lon_east":  se_lon,
    }


# ── Hintergrund-Datensammlung ─────────────────────────────────────────────────

def _sc_collect_data(egrid, radius_m, step_m, progress_cb=None, map_type="map"):
    """Läuft im Hintergrund-Thread. Gibt rohe Geodaten zurück (kein bpy).
    map_type: 'satellite' = swissimage Luftbild, 'map' = swisstopo Landeskarte."""
    result = {}

    if progress_cb:
        progress_cb("[1/5] Parzellenzentrum suchen...")
    center_lat, center_lon, display_label = _sc_get_parcel_centroid(egrid)
    result["center_lat"] = center_lat
    result["center_lon"] = center_lon
    result["display_label"] = display_label

    if progress_cb:
        progress_cb("[2/5] Parzellenpolygon laden...")
    parcel_polygon_lv95 = _sc_get_parcel_polygon(egrid)
    result["parcel_polygon_lv95"] = parcel_polygon_lv95

    hadr_info = None
    if parcel_polygon_lv95:
        polygon_centroid_e, polygon_centroid_n = _sc_lv95_centroid(parcel_polygon_lv95)
        if progress_cb:
            progress_cb("[2/5] HADR-Punkt suchen...")
        hadr_info = _sc_get_hadr_point(parcel_polygon_lv95)
        if hadr_info:
            origin_e, origin_n = hadr_info["point_lv95"]
            origin_source = "hadr_point"
        else:
            origin_e, origin_n = polygon_centroid_e, polygon_centroid_n
            origin_source = "parcel_centroid"
    else:
        origin_e, origin_n = _sc_wgs84_to_lv95(center_lon, center_lat)
        origin_source = "search_centroid"

    result["origin_e"] = origin_e
    result["origin_n"] = origin_n
    result["origin_source"] = origin_source
    result["hadr_info"] = hadr_info
    center_lon_f, center_lat_f = _sc_lv95_to_wgs84_approx(origin_e, origin_n)
    result["origin_lon"] = center_lon_f
    result["origin_lat"] = center_lat_f

    if progress_cb:
        progress_cb(f"[3/5] Terrain ({radius_m + _SC_TERRAIN_MARGIN_M:.0f} m, {step_m} m-Raster)...")
    terrain_grid = _sc_fetch_terrain_heights(origin_e, origin_n, radius_m, step_m, progress_cb)
    result["terrain_grid"] = terrain_grid

    if progress_cb:
        progress_cb("[4/5] OSM-Daten + Satellitenbild laden...")
    buildings_elements, roads_elements = _sc_fetch_osm_data(center_lat, center_lon, radius_m)
    result["buildings_elements"] = buildings_elements
    result["roads_elements"] = roads_elements

    # Kartenkacheln laden – WMTS-Layer je nach map_type.
    # WICHTIG: um den Szenen-Ursprung (origin_lat/lon) zentrieren,
    # nicht um den SearchServer-Zentroid (center_lat/lon), damit UV-Mapping stimmt.
    sat_data = None
    wmts_layer = _SC_MAP_LAYER if map_type == "map" else _SC_SAT_LAYER
    result["map_type"] = map_type
    result["wmts_layer"] = wmts_layer
    try:
        half_m = radius_m + _SC_TERRAIN_MARGIN_M
        origin_lat_f = result["origin_lat"]
        origin_lon_f = result["origin_lon"]
        sat_data = _sc_fetch_all_tiles(origin_lat_f, origin_lon_f, half_m,
                                       progress_cb=progress_cb, layer=wmts_layer)
    except Exception as exc:
        print(f"  Kartenbild nicht verfügbar: {exc}")
    result["sat_data"] = sat_data

    result["egrid"] = egrid
    result["radius_m"] = radius_m

    if progress_cb:
        progress_cb("[5/5] Daten bereit – Szene wird gebaut...")
    return result


# ── Blender-Szene aufbauen (Main-Thread) ──────────────────────────────────────

def _sc_recalc_normals(mesh):
    bm2 = bmesh.new()
    bm2.from_mesh(mesh)
    bmesh.ops.recalc_face_normals(bm2, faces=bm2.faces)
    bm2.to_mesh(mesh)
    bm2.free()
    mesh.update()


def _sc_remove_collection_tree(collection):
    for child in list(collection.children):
        _sc_remove_collection_tree(child)
    for obj in list(collection.objects):
        bpy.data.objects.remove(obj, do_unlink=True)
    bpy.data.collections.remove(collection)


def _sc_set_coll_visible(coll_name: str, visible: bool) -> bool:
    """Setzt Viewport-Sichtbarkeit (hide_viewport) einer Layer-Collection.
    Durchsucht rekursiv ab der Root-Layer-Collection. Gibt True zurück wenn gefunden."""
    def _find(lc, name):
        if lc.name == name:
            return lc
        for ch in lc.children:
            r = _find(ch, name)
            if r:
                return r
        return None

    try:
        root_lc = bpy.context.view_layer.layer_collection
        lc = _find(root_lc, coll_name)
        if lc:
            lc.hide_viewport = not visible
            return True
    except Exception as exc:
        print(f"  _sc_set_coll_visible({coll_name}): {exc}")
    return False


def _sc_apply_default_visibility():
    """Setzt die Standard-Sichtbarkeit nach dem Import:
    Terrain=aus, Strassen=aus, Parzelle=an, Gebäude=an."""
    _sc_set_coll_visible(_SC_TERRAIN_COLL,   False)
    _sc_set_coll_visible(_SC_ROADS_COLL,     False)
    _sc_set_coll_visible(_SC_BUILDINGS_COLL, True)
    _sc_set_coll_visible(_SC_PARCEL_COLL,    True)
    _sc_set_coll_visible(_SC_HADR_COLL,      True)
    try:
        sc = bpy.context.scene.swiss_context_props
        sc.show_terrain   = False
        sc.show_roads     = False
        sc.show_buildings = True
        sc.show_parcel    = True
    except Exception:
        pass


def _sc_prepare_collections():
    scene = bpy.context.scene
    existing = bpy.data.collections.get(_SC_ROOT_COLL)
    if existing:
        _sc_remove_collection_tree(existing)
    root = bpy.data.collections.new(_SC_ROOT_COLL)
    scene.collection.children.link(root)
    sub = {}
    for name in (_SC_TERRAIN_COLL, _SC_BUILDINGS_COLL, _SC_ROADS_COLL, _SC_PARCEL_COLL, _SC_HADR_COLL):
        coll = bpy.data.collections.new(name)
        root.children.link(coll)
        sub[name] = coll
    return root, sub[_SC_TERRAIN_COLL], sub[_SC_BUILDINGS_COLL], sub[_SC_ROADS_COLL], sub[_SC_PARCEL_COLL], sub[_SC_HADR_COLL]


def _sc_ensure_material(name, rgba, roughness=0.9):
    mat = bpy.data.materials.get(name) or bpy.data.materials.new(name=name)
    mat.use_nodes = True
    bsdf = mat.node_tree.nodes.get("Principled BSDF")
    if bsdf:
        bsdf.inputs["Base Color"].default_value = rgba
        bsdf.inputs["Roughness"].default_value = roughness
    return mat


def _sc_assign_material(obj, mat):
    if not (obj.data and hasattr(obj.data, "materials")):
        return
    if obj.data.materials:
        obj.data.materials[0] = mat
    else:
        obj.data.materials.append(mat)


def _sc_build_height(tags):
    h = None
    raw_h = tags.get("height")
    if raw_h:
        m = re.search(r"-?\d+(?:\.\d+)?", str(raw_h).replace(",", "."))
        h = float(m.group(0)) if m else None
    if h is not None:
        return max(h, 2.5)
    raw_lv = tags.get("building:levels")
    if raw_lv:
        m = re.search(r"-?\d+(?:\.\d+)?", str(raw_lv).replace(",", "."))
        lv = float(m.group(0)) if m else None
        if lv is not None:
            return max(lv * _SC_DEFAULT_LEVEL_H, 2.5)
    return _SC_DEFAULT_BLD_H


def _sc_road_width(tags):
    raw_w = tags.get("width")
    if raw_w:
        m = re.search(r"-?\d+(?:\.\d+)?", str(raw_w).replace(",", "."))
        if m:
            return max(float(m.group(0)), 2.5)
    highway = tags.get("highway", "")
    defaults = {"motorway": 7.5, "trunk": 7.0, "primary": 6.0, "secondary": 5.5,
                "tertiary": 4.8, "residential": 4.0, "living_street": 3.5,
                "service": 3.0, "unclassified": 3.8, "road": 3.5}
    return defaults.get(highway, 3.0)


def _sc_create_terrain_mesh(terrain_grid, origin_e, origin_n, collection):
    tg = terrain_grid
    x_min, y_min, step = tg["x_min"], tg["y_min"], tg["step"]
    cols, rows, heights = tg["cols"], tg["rows"], tg["heights"]
    verts = [(x_min + col * step, y_min + row * step, heights[row][col]) for row in range(rows) for col in range(cols)]
    faces = [(row*cols+col, row*cols+col+1, (row+1)*cols+col+1, (row+1)*cols+col)
             for row in range(rows-1) for col in range(cols-1)]
    mesh = bpy.data.meshes.new("TerrainMesh")
    mesh.from_pydata(verts, [], faces)
    mesh.update()
    mesh.validate(verbose=False)
    obj = bpy.data.objects.new("Terrain", mesh)
    collection.objects.link(obj)
    sampler = _ScTerrainSampler(x_min, y_min, step, cols, rows, heights)
    return obj, sampler


def _sc_create_parcel_boundary(egrid, points_lv95, origin_e, origin_n, origin_z, collection, sampler):
    pts = _sc_clean_ring_xy([_sc_lv95_to_local_xy(e, n, origin_e, origin_n) for e, n in points_lv95])
    if len(pts) < 3:
        return None
    wall_h = 0.3
    np2 = len(pts)
    gz = [sampler.sample(x, y) + _SC_PARCEL_Z_OFFSET for x, y in pts]
    verts = [(x, y, gz[i]) for i, (x, y) in enumerate(pts)] + [(x, y, gz[i]+wall_h) for i, (x, y) in enumerate(pts)]
    faces = [(i, (i+1)%np2, np2+(i+1)%np2, np2+i) for i in range(np2)]
    mesh = bpy.data.meshes.new("ParcelBoundaryMesh_SC")
    mesh.from_pydata(verts, [], faces)
    mesh.update(); mesh.validate(verbose=False); _sc_recalc_normals(mesh)
    obj = bpy.data.objects.new(f"Parcel_{egrid}", mesh)
    collection.objects.link(obj)
    obj["egrid"] = egrid; obj["crs"] = _SC_SCENE_CRS
    return obj


def _sc_create_hadr_marker(hadr_info, collection):
    r, bz, tz = 0.35, 0.9, 1.25
    verts = [(0,0,0),(r,r,bz),(r,-r,bz),(-r,-r,bz),(-r,r,bz),(0,0,tz)]
    faces = [(0,1,2),(0,2,3),(0,3,4),(0,4,1),(1,2,5),(2,3,5),(3,4,5),(4,1,5)]
    mesh = bpy.data.meshes.new("HADRMarkerMesh_SC")
    mesh.from_pydata(verts, [], faces)
    mesh.update(); mesh.validate(verbose=False); _sc_recalc_normals(mesh)
    obj = bpy.data.objects.new("HADR_Point", mesh)
    collection.objects.link(obj)
    obj["source_layer"] = "hadr"
    obj["street_name"] = hadr_info.get("street_name", "")
    obj["house_number"] = hadr_info.get("house_number", "")
    return obj


def _sc_create_building(name, pts_xy, tags, collection, sampler):
    pts_xy = _sc_clean_ring_xy(pts_xy)
    if len(pts_xy) < 3:
        return None
    body_h = _sc_build_height(tags)
    gz = [sampler.sample(x, y) for x, y in pts_xy]
    avg_gz = sum(gz) / len(gz)
    roof_z = avg_gz + body_h
    n = len(pts_xy)
    verts = [(x, y, gz[i]) for i, (x, y) in enumerate(pts_xy)] + [(x, y, roof_z) for (x, y) in pts_xy]
    faces = [tuple(range(n, 2*n))] + [(i, (i+1)%n, n+(i+1)%n, n+i) for i in range(n)]
    mesh = bpy.data.meshes.new(name)
    mesh.from_pydata(verts, [], faces)
    mesh.update(); mesh.validate(verbose=False); _sc_recalc_normals(mesh)
    obj = bpy.data.objects.new(name, mesh)
    collection.objects.link(obj)
    return obj


def _sc_create_road(name, pts_xy, tags, collection, sampler):
    if len(pts_xy) < 2:
        return None
    half_w = _sc_road_width(tags) / 2.0
    tangents = []
    for i in range(len(pts_xy)):
        if i == 0:
            dx, dy = pts_xy[1][0]-pts_xy[0][0], pts_xy[1][1]-pts_xy[0][1]
        elif i == len(pts_xy)-1:
            dx, dy = pts_xy[-1][0]-pts_xy[-2][0], pts_xy[-1][1]-pts_xy[-2][1]
        else:
            dx, dy = pts_xy[i+1][0]-pts_xy[i-1][0], pts_xy[i+1][1]-pts_xy[i-1][1]
        tangents.append(_sc_normalize2d(dx, dy))
    verts = []
    for i, (x, y) in enumerate(pts_xy):
        tx, ty = tangents[i]; nx, ny = -ty, tx
        z = sampler.sample(x, y) + _SC_ROAD_Z_OFFSET
        verts += [(x+nx*half_w, y+ny*half_w, z), (x-nx*half_w, y-ny*half_w, z)]
    faces = [(2*i, 2*i+2, 2*i+3, 2*i+1) for i in range(len(pts_xy)-1)]
    mesh = bpy.data.meshes.new(name)
    mesh.from_pydata(verts, [], faces)
    mesh.update(); mesh.validate(verbose=False); _sc_recalc_normals(mesh)
    obj = bpy.data.objects.new(name, mesh)
    collection.objects.link(obj)
    return obj


def _sc_import_buildings(elements, collection, origin_e, origin_n, sampler, material, parcel_local=None):
    rel_way_ids = {
        m.get("ref")
        for el in elements if el.get("type") == "relation"
        for m in el.get("members", []) if m.get("type") == "way" and m.get("role") in ("outer", "")
    }
    created = 0
    for el in elements:
        tags = el.get("tags", {})
        el_type, el_id = el.get("type"), el["id"]
        if el_type == "way":
            if el_id in rel_way_ids:
                continue
            pts = [_sc_lonlat_to_local_xy(p["lon"], p["lat"], origin_e, origin_n) for p in el.get("geometry", [])]
            obj = _sc_create_building(f"bld_way_{el_id}", pts, tags, collection, sampler)
            if obj:
                _sc_assign_material(obj, material); created += 1
        elif el_type == "relation":
            idx = 0
            for m in el.get("members", []):
                if m.get("type") != "way" or m.get("role") not in ("outer", ""):
                    continue
                geom = m.get("geometry", [])
                if not geom:
                    continue
                pts = [_sc_lonlat_to_local_xy(p["lon"], p["lat"], origin_e, origin_n) for p in geom]
                obj = _sc_create_building(f"bld_rel_{el_id}_{idx}", pts, tags, collection, sampler)
                if obj:
                    _sc_assign_material(obj, material); created += 1; idx += 1
    return created


def _sc_import_roads(elements, collection, origin_e, origin_n, sampler, material):
    created = 0
    for el in elements:
        if el.get("type") != "way":
            continue
        geom = el.get("geometry", [])
        if len(geom) < 2:
            continue
        pts = [_sc_lonlat_to_local_xy(p["lon"], p["lat"], origin_e, origin_n) for p in geom]
        obj = _sc_create_road(f"road_{el['id']}", pts, el.get("tags", {}), collection, sampler)
        if obj:
            _sc_assign_material(obj, material); created += 1
    return created


def _sc_create_satellite_material(image):
    """Erstellt ein Principled-BSDF-Material mit der Satellitentextur (UV-Map: SatelliteUV)."""
    mat_name = "SC_Satellite_Mat"
    existing = bpy.data.materials.get(mat_name)
    if existing:
        bpy.data.materials.remove(existing)
    mat = bpy.data.materials.new(mat_name)
    mat.use_nodes = True
    nodes = mat.node_tree.nodes
    links = mat.node_tree.links
    nodes.clear()
    output   = nodes.new("ShaderNodeOutputMaterial")
    bsdf     = nodes.new("ShaderNodeBsdfPrincipled")
    tex_node = nodes.new("ShaderNodeTexImage")
    uv_node  = nodes.new("ShaderNodeUVMap")
    tex_node.image = image
    uv_node.uv_map = "SatelliteUV"
    bsdf.inputs["Roughness"].default_value = 1.0
    links.new(uv_node.outputs["UV"],     tex_node.inputs["Vector"])
    links.new(tex_node.outputs["Color"], bsdf.inputs["Base Color"])
    links.new(bsdf.outputs["BSDF"],      output.inputs["Surface"])
    output.location  = (300,  0); bsdf.location    = (0,   0)
    tex_node.location = (-320,  0); uv_node.location  = (-570, 0)
    return mat


def _sc_stitch_and_apply_satellite(terrain_obj, sat_data, origin_e, origin_n, terrain_grid):
    """
    Fügt WMTS-Kacheln (swisstopo swissimage) zu einem Blender-Image zusammen
    und zieht es als UV-Textur über das Terrain-Mesh.

    Koordinatensystem-Logik:
      • WMTS-Kacheln: y_tile steigt südwärts  (y_min = nördlichste Kachel)
      • Blender-Images: Zeile 0 = Süden        (Zeile 0 = unterste Bildzeile)
      • JPEG-Dateien:   Zeile 0 = Norden       → Blender kehrt beim Laden automatisch um
      → Nach dem Load: tile_img.pixels[Zeile 0] = südlicher Rand der Kachel ✓
    """
    tiles     = sat_data["tiles"]
    x_min_t   = sat_data["x_min"];  y_min_t = sat_data["y_min"]
    x_max_t   = sat_data["x_max"];  y_max_t = sat_data["y_max"]
    lat_north = sat_data["lat_north"]; lat_south = sat_data["lat_south"]
    lon_west  = sat_data["lon_west"];  lon_east  = sat_data["lon_east"]
    lat_span  = max(lat_north - lat_south, 1e-9)
    lon_span  = max(lon_east  - lon_west,  1e-9)

    TILE_PX = 256
    cols_t  = x_max_t - x_min_t + 1
    rows_t  = y_max_t - y_min_t + 1
    total_w = cols_t * TILE_PX
    total_h = rows_t * TILE_PX

    # Grüner Füllpuffer als Fallback wenn Kacheln fehlen
    final_buf = _array_mod.array('f', [0.30, 0.45, 0.28, 1.0] * (total_w * total_h))

    tmp_dir = tempfile.mkdtemp(prefix="blender_sc_sat_")
    loaded_ok = 0
    try:
        for tx, ty, tile_bytes in tiles:
            if not tile_bytes:
                continue
            col_start = (tx - x_min_t) * TILE_PX
            row_start = (y_max_t - ty) * TILE_PX   # ty=y_min_t → ganz oben, ty=y_max_t → ganz unten

            tmp_path = os.path.join(tmp_dir, f"t_{tx}_{ty}.jpg")
            try:
                with open(tmp_path, "wb") as fh:
                    fh.write(tile_bytes)

                tile_img = bpy.data.images.load(tmp_path, check_existing=False)
                tile_img.colorspace_settings.name = "sRGB"

                # Sicherstellen dass Bilddaten geladen sind
                if not tile_img.has_data:
                    tile_img.pixels[0]  # triggert Load
                w, h = tile_img.size[0], tile_img.size[1]
                if w == 0 or h == 0:
                    bpy.data.images.remove(tile_img)
                    continue

                # Pixel als float-Array lesen (Blender: RGBA, Zeile 0 = Süd)
                n_px = w * h * 4
                tile_buf = _array_mod.array('f', [0.0] * n_px)
                tile_img.pixels.foreach_get(tile_buf)
                bpy.data.images.remove(tile_img)

                # Kachel-Pixel in final_buf einsetzen (zeilenweise, mit Größen-Anpassung)
                for r in range(h):
                    # Skalierung falls Kachel ≠ 256 px
                    dst_r = int(r * TILE_PX / h) if h != TILE_PX else r
                    dst_row = row_start + dst_r
                    if not (0 <= dst_row < total_h):
                        continue
                    dst_off = (dst_row * total_w + col_start) * 4
                    src_off = r * w * 4
                    row_data = tile_buf[src_off: src_off + min(w, TILE_PX) * 4]
                    final_buf[dst_off: dst_off + len(row_data)] = row_data

                loaded_ok += 1
            except Exception as exc:
                print(f"  Sat-Kachel {tx}/{ty} fehlgeschlagen: {exc}")
            finally:
                try:
                    os.unlink(tmp_path)
                except Exception:
                    pass
    finally:
        try:
            os.rmdir(tmp_dir)
        except Exception:
            pass

    if loaded_ok == 0:
        print("  Keine Satellitenkacheln geladen – Terrain bleibt grün.")
        return None

    # ── Blender-Image erstellen und Pixel setzen ──────────────────────────────
    img_name = "SC_Satellite"
    existing = bpy.data.images.get(img_name)
    if existing:
        bpy.data.images.remove(existing)
    final_img = bpy.data.images.new(img_name, width=total_w, height=total_h, alpha=False)
    final_img.colorspace_settings.name = "sRGB"
    final_img.pixels.foreach_set(final_buf)
    final_img.pack()   # im .blend eingebettet, kein externer Pfad nötig

    # ── UV-Map auf dem Terrain-Mesh berechnen ────────────────────────────────
    mesh    = terrain_obj.data
    uv_name = "SatelliteUV"
    if uv_name not in mesh.uv_layers:
        mesh.uv_layers.new(name=uv_name)
    uv_layer = mesh.uv_layers[uv_name]

    tg        = terrain_grid
    x_min_loc = tg["x_min"]; y_min_loc = tg["y_min"]
    step      = tg["step"];  cols = tg["cols"]; rows = tg["rows"]

    # UV pro Vertex (Index = row*cols + col, identisch mit _sc_create_terrain_mesh)
    vertex_uvs = []
    for row in range(rows):
        for col in range(cols):
            lon, lat = _sc_lv95_to_wgs84_approx(
                origin_e + x_min_loc + col * step,
                origin_n + y_min_loc + row * step,
            )
            u = max(0.0, min(1.0, (lon - lon_west)  / lon_span))
            v = max(0.0, min(1.0, (lat - lat_south) / lat_span))
            vertex_uvs.append((u, v))

    # UV pro Loop setzen (jede Fläche hat 4 Loops)
    for loop in mesh.loops:
        vi = loop.vertex_index
        if vi < len(vertex_uvs):
            uv_layer.data[loop.index].uv = vertex_uvs[vi]

    mesh.update()

    # ── Material anwenden ────────────────────────────────────────────────────
    sat_mat = _sc_create_satellite_material(final_img)
    if terrain_obj.data.materials:
        terrain_obj.data.materials[0] = sat_mat
    else:
        terrain_obj.data.materials.append(sat_mat)

    print(f"  Satellitentextur angewendet: {loaded_ok}/{len(tiles)} Kacheln, {total_w}×{total_h}px")
    return sat_mat


def _sc_build_scene(data):
    """Baut die komplette Blender-Szene aus den vorgesammelten Rohdaten. Läuft im Main-Thread."""
    egrid       = data["egrid"]
    origin_e    = data["origin_e"]
    origin_n    = data["origin_n"]
    parcel_poly = data.get("parcel_polygon_lv95")
    hadr_info   = data.get("hadr_info")
    terrain_grd = data["terrain_grid"]

    root_coll, terrain_coll, buildings_coll, roads_coll, parcel_coll, hadr_coll = _sc_prepare_collections()

    mat_terrain  = _sc_ensure_material("SC_Terrain_Mat",  (0.38, 0.47, 0.30, 1.0))
    mat_building = _sc_ensure_material("SC_Building_Mat", (0.78, 0.77, 0.72, 1.0))
    mat_road     = _sc_ensure_material("SC_Road_Mat",     (0.12, 0.12, 0.12, 1.0))
    mat_parcel   = _sc_ensure_material("SC_Parcel_Mat",   (0.85, 0.10, 0.05, 1.0), roughness=0.5)
    mat_hadr     = _sc_ensure_material("SC_HADR_Mat",     (0.06, 0.42, 0.95, 1.0), roughness=0.35)

    terrain_obj, sampler = _sc_create_terrain_mesh(terrain_grd, origin_e, origin_n, terrain_coll)
    origin_z = sampler.sample_absolute(0.0, 0.0)
    sampler.set_z_offset(origin_z)
    for v in terrain_obj.data.vertices:
        v.co.z -= origin_z
    terrain_obj.data.update()
    _sc_assign_material(terrain_obj, mat_terrain)

    if parcel_poly:
        parcel_obj = _sc_create_parcel_boundary(egrid, parcel_poly, origin_e, origin_n, origin_z, parcel_coll, sampler)
        if parcel_obj:
            _sc_assign_material(parcel_obj, mat_parcel)

    if hadr_info:
        hadr_obj = _sc_create_hadr_marker(hadr_info, hadr_coll)
        _sc_assign_material(hadr_obj, mat_hadr)

    bld_count = _sc_import_buildings(
        data["buildings_elements"], buildings_coll, origin_e, origin_n, sampler, mat_building)
    road_count = _sc_import_roads(
        data["roads_elements"], roads_coll, origin_e, origin_n, sampler, mat_road)

    # Satellitenbild als Terrain-Textur (falls vorhanden)
    sat_data = data.get("sat_data")
    if sat_data and sat_data.get("tiles"):
        try:
            sat_mat = _sc_stitch_and_apply_satellite(terrain_obj, sat_data, origin_e, origin_n, terrain_grd)
            if sat_mat:
                try:
                    bpy.context.scene.swiss_context_props.satellite_visible = True
                except Exception:
                    pass
                # Viewport auf Material Preview umschalten damit Textur sichtbar ist
                for area in bpy.context.screen.areas:
                    if area.type == "VIEW_3D":
                        for space in area.spaces:
                            if space.type == "VIEW_3D" and space.shading.type == "SOLID":
                                space.shading.type = "MATERIAL"
                        break
        except Exception as exc:
            print(f"  Satellitentextur konnte nicht angewendet werden: {exc}")

    bpy.context.scene.unit_settings.system = "METRIC"
    bpy.context.scene.unit_settings.scale_length = 1.0

    # Standard-Sichtbarkeit: Terrain + Strassen versteckt, Gebäude + Parzelle sichtbar
    _sc_apply_default_visibility()

    return bld_count, road_count


# ── PropertyGroup ─────────────────────────────────────────────────────────────

class SwissContextProperties(PropertyGroup):
    radius_m: bpy.props.IntProperty(
        name="Radius (m)", description="Umgebungsradius für OSM-Gebäude/Strassen", default=150, min=50, max=500)
    terrain_step: bpy.props.IntProperty(
        name="Terrain-Raster (m)", description="Rasterweite für das Geländemodell", default=10, min=5, max=50)
    import_status: StringProperty(name="Status", default="")
    is_importing: BoolProperty(name="Importiert", default=False)
    satellite_visible: BoolProperty(name="Kartenbild aktiv", default=False)
    map_type: bpy.props.EnumProperty(
        name="Kartenlayer",
        description="Welcher Kartentyp als Textur auf das Gelände gezogen wird",
        items=[
            ("map",       "Landeskarte",   "Swisstopo Pixelkarte farbig (wie Onlinekarte)"),
            ("satellite", "Satellitenbild","Luftbild swissimage"),
        ],
        default="map",
    )
    # Layer-Sichtbarkeit (Standardzustand nach Import)
    show_terrain:   BoolProperty(name="Gelände",  default=False)
    show_roads:     BoolProperty(name="Strassen", default=False)
    show_buildings: BoolProperty(name="Gebäude",  default=True)
    show_parcel:    BoolProperty(name="Parzelle", default=True)


# ── Operator: Satellitenbild ein/ausblenden ───────────────────────────────────

class SWISSCONTEXT_OT_toggle_satellite(Operator):
    bl_idname     = "parcel_workflow.swiss_context_toggle_sat"
    bl_label      = "Satellitenbild ein/ausblenden"
    bl_description = "Wechselt zwischen Satellitentextur und Erd-Farbe auf dem Terrain"

    def execute(self, context):
        sc_props = context.scene.swiss_context_props

        # Terrain-Objekt suchen (in Swiss_Context_LV95 → Terrain)
        terrain_obj = None
        root_coll = bpy.data.collections.get(_SC_ROOT_COLL)
        if root_coll:
            for sub in root_coll.children:
                if sub.name == _SC_TERRAIN_COLL:
                    for obj in sub.objects:
                        if obj.type == "MESH":
                            terrain_obj = obj
                            break

        if terrain_obj is None:
            self.report({"WARNING"}, "Kein Terrain gefunden – bitte zuerst Umgebung importieren.")
            return {"CANCELLED"}

        sc_props.satellite_visible = not sc_props.satellite_visible

        if sc_props.satellite_visible:
            mat = bpy.data.materials.get("SC_Satellite_Mat")
            if mat is None:
                sc_props.satellite_visible = False
                self.report({"WARNING"}, "Satellitenbild-Material nicht gefunden – Umgebung neu importieren.")
                return {"CANCELLED"}
        else:
            mat = bpy.data.materials.get("SC_Terrain_Mat")
            if mat is None:
                mat = _sc_ensure_material("SC_Terrain_Mat", (0.38, 0.47, 0.30, 1.0))

        if terrain_obj.data.materials:
            terrain_obj.data.materials[0] = mat
        else:
            terrain_obj.data.materials.append(mat)

        redraw_ui()
        return {"FINISHED"}


# ── Operator: Layer ein/ausblenden ────────────────────────────────────────────

class SWISSCONTEXT_OT_toggle_layer(Operator):
    """Blendet eine Umgebungs-Layer-Collection ein oder aus."""
    bl_idname      = "parcel_workflow.swiss_context_toggle_layer"
    bl_label       = "Layer ein/ausblenden"
    bl_description = "Schaltet die Sichtbarkeit des gewählten Layers um"

    target: StringProperty(
        name="Ziel",
        description="terrain | roads | buildings | parcel | map",
        default="",
    )

    def execute(self, context):
        sc = context.scene.swiss_context_props

        if self.target == "terrain":
            sc.show_terrain = not sc.show_terrain
            _sc_set_coll_visible(_SC_TERRAIN_COLL, sc.show_terrain)

        elif self.target == "roads":
            sc.show_roads = not sc.show_roads
            _sc_set_coll_visible(_SC_ROADS_COLL, sc.show_roads)

        elif self.target == "buildings":
            sc.show_buildings = not sc.show_buildings
            _sc_set_coll_visible(_SC_BUILDINGS_COLL, sc.show_buildings)

        elif self.target == "parcel":
            sc.show_parcel = not sc.show_parcel
            _sc_set_coll_visible(_SC_PARCEL_COLL, sc.show_parcel)
            _sc_set_coll_visible(_SC_HADR_COLL,   sc.show_parcel)

        redraw_ui()
        return {"FINISHED"}


# ── Operator: Hauptimport ─────────────────────────────────────────────────────

class SWISSCONTEXT_OT_import(Operator):
    bl_idname  = "parcel_workflow.swiss_context_import"
    bl_label   = "Umgebung importieren"
    bl_description = "Importiert Gelände, Gebäude und Strassen der Umgebung via swisstopo/OSM (läuft im Hintergrund)"

    _timer   = None
    _thread  = None
    _result  = None
    _error   = None
    _done    = False
    _start_t = 0.0

    def _cleanup(self, context):
        if self._timer is not None:
            context.window_manager.event_timer_remove(self._timer)
            self._timer = None
        redraw_ui()

    def modal(self, context, event):
        sc_props = context.scene.swiss_context_props
        if event.type != "TIMER":
            return {"PASS_THROUGH"}
        elapsed = int(time.time() - self._start_t)
        if not self._done:
            sc_props.import_status = f"⏳ {sc_props.import_status or 'Daten werden geladen...'} ({elapsed}s)"
            redraw_ui()
            return {"RUNNING_MODAL"}
        # Thread fertig
        self._cleanup(context)
        sc_props.is_importing = False
        if self._error:
            sc_props.import_status = f"Fehler: {self._error}"
            self.report({"ERROR"}, str(self._error))
            return {"CANCELLED"}
        try:
            bld, rds = _sc_build_scene(self._result)
            sc_props.import_status = f"Fertig: {bld} Gebäude, {rds} Strassen ({elapsed}s)"
            self.report({"INFO"}, sc_props.import_status)
        except Exception as exc:
            sc_props.import_status = f"Fehler beim Szenenaufbau: {exc}"
            self.report({"ERROR"}, str(exc))
            return {"CANCELLED"}
        redraw_ui()
        return {"FINISHED"}

    def execute(self, context):
        sc_props = context.scene.swiss_context_props
        pw_props = context.scene.parcel_workflow
        if sc_props.is_importing:
            self.report({"WARNING"}, "Import läuft bereits.")
            return {"CANCELLED"}

        # EGRID bestimmen: zuerst props.egrid, sonst aus GeoJSON
        egrid = (pw_props.egrid or "").strip().upper()
        if not (len(egrid) == 14 and egrid.startswith("CH") and egrid[2:].isdigit()):
            # Aus GeoJSON versuchen
            geojson_path_str = pw_props.geojson_path or ""
            if geojson_path_str:
                geojson_path_p = Path(bpy.path.abspath(geojson_path_str))
                if geojson_path_p.exists():
                    egrid = egrid_from_geojson(geojson_path_p) or ""
        if not (len(egrid) == 14 and egrid.startswith("CH") and egrid[2:].isdigit()):
            self.report({"ERROR"}, "Keine gültige EGRID gefunden. Bitte EGRID im Docker-Download-Feld eingeben oder GeoJSON laden.")
            return {"CANCELLED"}

        radius_m = sc_props.radius_m
        step_m   = sc_props.terrain_step

        self._result = None
        self._error  = None
        self._done   = False
        self._start_t = time.time()
        sc_props.is_importing = True
        sc_props.import_status = "Starte..."

        def _progress_cb(msg):
            # Darf nur gelesen werden; StringProperty update aus Thread (indirekt)
            sc_props.import_status = str(msg)

        map_type = sc_props.map_type  # "map" oder "satellite"

        def _run():
            try:
                self._result = _sc_collect_data(egrid, radius_m, float(step_m),
                                                _progress_cb, map_type=map_type)
            except Exception as exc:
                self._error = str(exc)
            finally:
                self._done = True

        self._thread = threading.Thread(target=_run, daemon=True)
        self._thread.start()
        self._timer = context.window_manager.event_timer_add(0.5, window=context.window)
        context.window_manager.modal_handler_add(self)
        return {"RUNNING_MODAL"}


# ── Ende Swiss Context Block ──────────────────────────────────────────────────


class PARCELWORKFLOW_PT_panel(Panel):
    bl_label = "Parcel Workflow"
    bl_idname = "PARCELWORKFLOW_PT_panel"
    bl_space_type = "VIEW_3D"
    bl_region_type = "UI"
    bl_category = "Parcel"

    def draw(self, context):
        layout = self.layout
        props = context.scene.parcel_workflow

        # ── Docker Download ───────────────────────────────────────
        box_docker = layout.box()
        box_docker.label(text="Docker Download", icon="CONSOLE")
        box_docker.prop(props, "project_root")
        row_ct = box_docker.row(align=True)
        row_ct.prop(props, "canton")
        row_ct.prop(props, "egrid")
        row_dl = box_docker.row()
        row_dl.enabled = not props.docker_busy
        row_dl.operator("parcel_workflow.run_docker", text="Download starten", icon="IMPORT")
        if props.resolved_project_root:
            box_docker.label(text=f"Projekt: {Path(props.resolved_project_root).name}", icon="FILE_FOLDER")
        box_docker.label(text=props.docker_status or "Bereit.")
        if props.last_downloaded_gpkg:
            box_docker.label(text=f"GPKG: {Path(props.last_downloaded_gpkg).name}", icon="FILE")

        layout.separator(factor=0.5)

        # ── Parzelle importieren ──────────────────────────────────
        box_import = layout.box()
        box_import.label(text="Parzelle importieren", icon="WORLD")
        box_import.prop(props, "gpkg_path")
        box_import.prop(props, "geojson_path")
        box_import.prop(props, "action_mode", text="")
        box_import.operator("parcel_workflow.run", text="Aktion ausführen", icon="PLAY")
        if props.last_import_collection:
            box_import.label(text=f"Collection: {props.last_import_collection}", icon="OUTLINER_COLLECTION")
        if props.last_origin_e and props.last_origin_n:
            row_orig = box_import.row()
            row_orig.label(text=f"E: {props.last_origin_e}")
            row_orig.label(text=f"N: {props.last_origin_n}")

        layout.separator(factor=0.5)

        # ── ÖREB & Bauverordnung ──────────────────────────────────
        box_oereb = layout.box()
        box_oereb.label(text="ÖREB & Bauverordnung", icon="INFO")
        gemeinde_name = props.gemeinde or props.last_oereb_municipality
        if gemeinde_name:
            box_oereb.label(text=f"Gemeinde: {gemeinde_name}", icon="HOME")
        if props.last_nutzungszone:
            box_oereb.label(text=f"Zone: {props.last_nutzungszone}", icon="MESH_GRID")
        box_oereb.operator("parcel_workflow.open_bauverordnung", text="Bauverordnung suchen", icon="URL")

        layout.separator(factor=0.5)

        # ── IFC Import ────────────────────────────────────────────
        box_ifc = layout.box()
        box_ifc.label(text="IFC Import", icon="FILE_3D")
        box_ifc.prop(props, "ifc_path")
        box_ifc.prop(props, "remove_ifc_terrain")
        box_ifc.operator("parcel_workflow.import_ifc", text="IFC importieren", icon="IMPORT")
        if props.last_ifc_import:
            box_ifc.label(text=f"Letztes IFC: {Path(props.last_ifc_import).name}", icon="FILE")

        layout.separator(factor=0.5)

        # ── Grenzabstand-Check ────────────────────────────────────
        gc = context.scene.grenzcheck_props
        box_gc = layout.box()
        box_gc.label(text="Grenzabstand-Check", icon="SNAP_EDGE")

        # Erkannte Objekte (kompakt)
        scene = context.scene
        own_gc       = _gc_find_target_parcel(scene)
        neighbors_gc = _gc_find_neighbors(scene)
        buildings_gc = _gc_get_buildings(scene, gc.collection_keyword)
        row_own = box_gc.row()
        row_own.label(text="Bauparzelle:", icon="HOME")
        row_own.label(text=_gc_short(own_gc.name, 20) if own_gc else "⚠ nicht gefunden",
                      icon="CHECKMARK" if own_gc else "ERROR")
        row_nb = box_gc.row()
        row_nb.label(text="Nachbarn:", icon="MESH_GRID")
        row_nb.label(text=f"{len(neighbors_gc)}", icon="CHECKMARK" if neighbors_gc else "ERROR")
        row_bld = box_gc.row()
        row_bld.label(text="IFC-Gebäude:", icon="OUTLINER_OB_MESH")
        row_bld.label(text=f"{len(buildings_gc)}", icon="CHECKMARK" if buildings_gc else "ERROR")

        # Collection-Stichwort
        box_gc.prop(gc, "collection_keyword", text="IFC-Collection")

        # Grenzabstände
        row_g = box_gc.row(align=True)
        row_g.prop(gc, "grenzabstand_gross", text="Hauptwohnseite m")
        row_k = box_gc.row(align=True)
        row_k.prop(gc, "grenzabstand_klein", text="Übrige Seiten m")
        if gc.grenzabstand_klein >= gc.grenzabstand_gross:
            row_warn = box_gc.row(); row_warn.alert = True
            row_warn.label(text="⚠ Klein muss < Gross sein!", icon="ERROR")

        # Haupt-Button
        big = box_gc.row()
        big.scale_y = 1.4
        big.operator("parcel_workflow.grenzcheck_run", icon="CHECKMARK", text="Grenzabstand prüfen")

        # Visualisierung
        vis_row = box_gc.row(align=True)
        vis_row.operator("parcel_workflow.grenzcheck_visualize", icon="SHADING_BBOX", text="Visualisieren")
        vis_row.operator("parcel_workflow.grenzcheck_clear_vis", icon="TRASH", text="Löschen")

        # Letztes Ergebnis (nur Zusammenfassung)
        if gc.result_text:
            # Aktionen-Zeile
            act_row = box_gc.row(align=True)
            act_row.operator("parcel_workflow.grenzcheck_clear",
                             icon="X", text="Löschen")
            # Zusammenfassung
            res_box = box_gc.box()
            res_box.scale_y = 0.75
            in_summary = False
            for line in gc.result_text.split("\n"):
                if "ZUSAMMENFASSUNG" in line:
                    in_summary = True
                if in_summary:
                    res_box.label(text=line)

        layout.separator(factor=0.5)

        # ── Umgebung importieren (Swiss Context) ──────────────────
        sc = context.scene.swiss_context_props
        box_sc = layout.box()
        box_sc.label(text="Umgebung importieren", icon="WORLD_DATA")

        # Einstellungen: Radius, Raster, Kartentyp
        row_sc1 = box_sc.row(align=True)
        row_sc1.prop(sc, "radius_m",     text="Radius m")
        row_sc1.prop(sc, "terrain_step", text="Raster m")
        box_sc.prop(sc, "map_type", text="Karte")

        btn_sc = box_sc.row()
        btn_sc.enabled = not sc.is_importing
        btn_sc.scale_y = 1.3
        btn_sc.operator("parcel_workflow.swiss_context_import", icon="WORLD_DATA", text="Umgebung importieren")

        # Layer-Steuerung (nur sichtbar wenn Umgebung vorhanden)
        if bpy.data.collections.get(_SC_ROOT_COLL):
            box_sc.separator(factor=0.3)
            box_sc.label(text="Layer ein/ausblenden:", icon="RENDERLAYERS")

            # Zeile 1: Kartenbild-Toggle (Satellit/Karte)
            map_row = box_sc.row(align=True)
            if sc.satellite_visible:
                map_row.operator("parcel_workflow.swiss_context_toggle_sat",
                                 text="Kartenbild aus", icon="HIDE_OFF")
            else:
                map_row.operator("parcel_workflow.swiss_context_toggle_sat",
                                 text="Kartenbild ein", icon="HIDE_ON")

            # Zeile 2: Gebäude | Parzelle
            row2 = box_sc.row(align=True)
            bld_icon = "HIDE_OFF" if sc.show_buildings else "HIDE_ON"
            op = row2.operator("parcel_workflow.swiss_context_toggle_layer",
                               text="Gebäude", icon=bld_icon)
            op.target = "buildings"
            par_icon = "HIDE_OFF" if sc.show_parcel else "HIDE_ON"
            op = row2.operator("parcel_workflow.swiss_context_toggle_layer",
                               text="Parzelle", icon=par_icon)
            op.target = "parcel"

            # Zeile 3: Strassen | Gelände
            row3 = box_sc.row(align=True)
            rds_icon = "HIDE_OFF" if sc.show_roads else "HIDE_ON"
            op = row3.operator("parcel_workflow.swiss_context_toggle_layer",
                               text="Strassen", icon=rds_icon)
            op.target = "roads"
            ter_icon = "HIDE_OFF" if sc.show_terrain else "HIDE_ON"
            op = row3.operator("parcel_workflow.swiss_context_toggle_layer",
                               text="Gelände", icon=ter_icon)
            op.target = "terrain"

        if sc.import_status:
            box_sc.label(text=sc.import_status,
                         icon="INFO" if not sc.import_status.startswith("Fehler") else "ERROR")

        layout.separator(factor=0.5)

        # ── PDF-Bericht ───────────────────────────────────────────────────────
        box_pdf = layout.box()
        box_pdf.label(text="PDF-Bericht", icon="FILE_TEXT")

        parcel_props = context.scene.parcel_workflow
        cam_row = box_pdf.row()
        cam_row.scale_y = 1.2
        cam_row.operator("parcel_workflow.grenzcheck_create_cameras",
                         icon="CAMERA_DATA", text="4 Kameras erstellen")

        pdf_row = box_pdf.row()
        pdf_row.scale_y = 1.4
        pdf_row.operator("parcel_workflow.grenzcheck_export_pdf",
                         icon="FILE_TEXT", text="PDF-Bericht erstellen")

        if gc.pdf_status:
            is_err = "fehlgeschlagen" in gc.pdf_status or gc.pdf_status.startswith("Fehler")
            box_pdf.label(text=gc.pdf_status,
                          icon="ERROR" if is_err else "CHECKMARK")


classes = (
    ParcelWorkflowProperties,
    GrenzcheckProperties,
    SwissContextProperties,
    PARCELWORKFLOW_OT_run_docker,
    PARCELWORKFLOW_OT_run,
    PARCELWORKFLOW_OT_open_bauverordnung,
    PARCELWORKFLOW_OT_import_ifc,
    GRENZCHECK_OT_run,
    GRENZCHECK_OT_visualize,
    GRENZCHECK_OT_clear_vis,
    GRENZCHECK_OT_clear,
    GRENZCHECK_OT_create_cameras,
    GRENZCHECK_OT_export_pdf,
    SWISSCONTEXT_OT_import,
    SWISSCONTEXT_OT_toggle_satellite,
    SWISSCONTEXT_OT_toggle_layer,
    PARCELWORKFLOW_PT_panel,
)


def register():
    for cls in classes:
        bpy.utils.register_class(cls)
    bpy.types.Scene.parcel_workflow    = PointerProperty(type=ParcelWorkflowProperties)
    bpy.types.Scene.grenzcheck_props   = PointerProperty(type=GrenzcheckProperties)
    bpy.types.Scene.swiss_context_props = PointerProperty(type=SwissContextProperties)


def unregister():
    del bpy.types.Scene.parcel_workflow
    del bpy.types.Scene.grenzcheck_props
    del bpy.types.Scene.swiss_context_props
    for cls in reversed(classes):
        bpy.utils.unregister_class(cls)


if __name__ == "__main__":
    register()
