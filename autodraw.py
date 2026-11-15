# -*- coding: utf-8 -*-
"""
AutoDraw Studio 3  -  рисует любую картинку в браузерных играх
(Gartic Phone, Skribbl.io, Drawaria и др.) плавно и аккуратно, как человек.

Установка:  pip install customtkinter pillow numpy pynput
Запуск:     python autodraw.py
Сборка:     build_exe.bat  (один файл .exe через PyInstaller)

Горячие клавиши (работают поверх любых окон):
    F8  - начать рисование
    F9  - пауза / продолжить
    Esc - экстренная остановка
"""
from __future__ import annotations

import copy
import hashlib
import itertools
import json
import math
import os
import queue
import random
import re
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import urllib.request
from dataclasses import dataclass

IS_WIN = sys.platform == "win32"
FROZEN = bool(getattr(sys, "frozen", False))

if IS_WIN:
    import ctypes
    from ctypes import wintypes

    try:  # реальные пиксели экрана при масштабе 125-150 %
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass
    try:  # точный системный таймер (паузы ~1 мс)
        ctypes.windll.winmm.timeBeginPeriod(1)
    except Exception:
        pass
    try:  # своя иконка на панели задач, а не иконка Python
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("AutoDrawStudio.App")
    except Exception:
        pass

import tkinter as tk
import tkinter.font as tkfont
from tkinter import filedialog, messagebox

try:
    import customtkinter as ctk
    import numpy as np
    from PIL import Image, ImageDraw, ImageEnhance, ImageFilter, ImageGrab
    from pynput import keyboard
except ImportError:
    print("Не хватает библиотек. Установите их одной командой:\n"
          "    pip install customtkinter pillow numpy pynput")
    input("Нажмите Enter для выхода...")
    sys.exit(1)

# совместимость разных версий Pillow
LANCZOS = getattr(Image, "Resampling", Image).LANCZOS
_QZ = getattr(Image, "Quantize", None)
MEDIANCUT = _QZ.MEDIANCUT if _QZ else 0
_DT = getattr(Image, "Dither", None)
DITHER_FS = _DT.FLOYDSTEINBERG if _DT else 3
DITHER_NONE = _DT.NONE if _DT else 0


# =============================================================================
#  Константы и настройки
# =============================================================================
APP_NAME = "AutoDraw Studio"
APP_VERSION = "3.0.0"
# Автообновление: укажите "логин/репозиторий" на GitHub, где вы публикуете релизы.
# Пустая строка = проверка обновлений выключена.
UPDATE_REPO = "KrasilLito/GarticBot"

APP_DIR = os.path.dirname(os.path.abspath(sys.executable if FROZEN else sys.argv[0]))
CFG_PATH = os.path.join(APP_DIR, "autodraw_studio.json")


def resource_path(name: str) -> str:
    """Путь к файлу рядом с программой или внутри собранного .exe."""
    return os.path.join(getattr(sys, "_MEIPASS", APP_DIR), name)


ICON_PATH = resource_path("autodraw.ico")

# Палитра интерфейса: спокойный тёмный фон, один мягкий акцент.
C_BG = "#0b0b0e"
C_SIDE = "#0f0f13"
C_SURFACE = "#15151a"
C_SURFACE2 = "#1c1c23"
C_HOVER = "#262630"
C_BORDER = "#22222a"
C_TEXT = "#ededf2"
C_MUTED = "#8f8f9c"
C_FAINT = "#5c5c69"
C_ACCENT = "#8b7cf6"
C_ACCENT_H = "#a093f9"
C_ACCENT_D = "#241f3d"
C_OK = "#4ade80"
C_WARN = "#fbbf24"
C_BAD = "#f87171"
C_BAD_H = "#fb9a9a"

MODES = ["Цвет + контур", "Только цвет", "Только контур"]
SRC_BTN, SRC_MY, SRC_AUTO = "Кнопки цветов", "Мои цвета (RGB)", "Авто из картинки"
SOURCES = [SRC_BTN, SRC_MY, SRC_AUTO]
SOURCE_HINTS = {
    SRC_BTN: "Нажимает на готовые кнопки цветов в игре. Укажите их кнопкой ◎ в списке ниже.",
    SRC_MY: "Вписывает ваши цвета из списка ниже в поля R, G, B палитры игры.",
    SRC_AUTO: "Сама подбирает лучшие цвета картинки и вписывает их в палитру игры. Самый точный вариант.",
}
CALIB_NAMES = {
    "canvas": "область холста", "picker_btn": "кнопка палитры", "field_r": "поле R",
    "field_g": "поле G", "field_b": "поле B", "thin_btn": "тонкая кисть",
    "thick_btn": "широкая кисть", "brush_tool": "инструмент «Кисть»",
    "fill_tool": "инструмент «Заливка»",
}
PAGES = (("Рисунок", "◐"), ("Калибровка", "◎"), ("Цвета", "◉"),
         ("Стиль", "✎"), ("Скорость", "➤"), ("О программе", "ⓘ"))
SPEED_NAMES = {1: "Бережно", 2: "Бережно", 3: "Спокойно", 4: "Спокойно", 5: "Обычно",
               6: "Обычно", 7: "Быстро", 8: "Быстро", 9: "Очень быстро", 10: "Максимум"}

BASE_COLORS = (
    ("Красный", (229, 34, 34)), ("Зелёный", (34, 177, 76)), ("Синий", (30, 90, 230)),
    ("Бежевый", (238, 207, 170)), ("Чёрный", (0, 0, 0)), ("Жёлтый", (255, 221, 0)),
)

DEFAULTS = {
    # калибровка (экранные координаты)
    "canvas": None, "picker_btn": None, "field_r": None, "field_g": None, "field_b": None,
    "brush_tool": None, "fill_tool": None, "thin_btn": None, "thick_btn": None,
    # картинка
    "mode": MODES[0], "brightness": 1.0, "contrast": 1.1, "saturation": 1.1,
    "despeckle": True, "min_area": 4,
    # цвета
    "color_src": SRC_AUTO, "auto_colors": 16, "white_thr": 238, "dither": False,
    "palette": [{"name": n, "rgb": list(c), "pos": None, "on": True, "custom": False}
                for n, c in BASE_COLORS],
    # кисти и стиль
    "thin_px": 4, "thick_px": 16, "use_thick": True, "overlap": 30,
    "use_bucket": True, "fill_safety": 1, "min_fill": 60,
    "sketch": True, "outline": True, "zigzag": True, "human": 60,
    "edge_thr": 40, "edge_min": 8, "smooth": 2,
    # скорость
    "speed": 8, "speed_auto": True,
    "color_pause": 180, "picker_pause": 300, "fill_pause": 150,
    # безопасность и окно
    "countdown": 3, "hide": True, "stop_on_move": True, "topmost": True,
    # обновления
    "auto_update": True, "skip_version": "", "update_repo": "", "last_version": "",
}

def load_settings() -> dict:
    cfg = copy.deepcopy(DEFAULTS)
    try:
        with open(CFG_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception:
        return cfg
    for key, default in DEFAULTS.items():
        if key not in data:
            continue
        val = data[key]
        try:
            if isinstance(default, bool):
                cfg[key] = bool(val)
            elif isinstance(default, int):
                cfg[key] = int(val)
            elif isinstance(default, float):
                cfg[key] = float(val)
            elif key == "palette":
                pal = [{"name": str(c["name"]), "rgb": [int(v) for v in c["rgb"]][:3],
                        "pos": c.get("pos"), "on": bool(c.get("on", True)),
                        "custom": bool(c.get("custom", False))} for c in val]
                cfg[key] = pal or cfg[key]
            else:
                cfg[key] = val
        except Exception:
            pass
    for key, allowed in (("mode", MODES), ("color_src", SOURCES)):
        if cfg[key] not in allowed:
            cfg[key] = DEFAULTS[key]
    cfg["speed"] = max(1, min(10, int(cfg["speed"])))
    return cfg


def save_settings(cfg: dict) -> None:
    try:
        with open(CFG_PATH, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
    except Exception as e:
        print("Не удалось сохранить настройки:", e)


# =============================================================================
#  Утилиты
# =============================================================================
def precise_sleep(sec: float) -> None:
    """Точная пауза: sleep для длинной части, активное ожидание для хвоста."""
    if sec <= 0:
        return
    end = time.perf_counter() + sec
    if sec > 0.003:
        time.sleep(sec - 0.002)
    while time.perf_counter() < end:
        pass


def to_px(v: float) -> int:
    """Округление до пикселя без «банковского» округления Python (иначе строки сливаются)."""
    return int(math.floor(v + 0.5))


def rgb_hex(rgb) -> str:
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(v))) for v in rgb)


def luminance(rgb) -> float:
    return 0.299 * rgb[0] + 0.587 * rgb[1] + 0.114 * rgb[2]


def min_jerk(t: float) -> float:
    """Профиль движения руки: плавный разгон и торможение."""
    return t * t * t * (10 - 15 * t + 6 * t * t)


def fmt_pos(p) -> str:
    if not p:
        return "не задано"
    if len(p) == 4:
        return f"{p[2] - p[0]}×{p[3] - p[1]} px"
    return f"{p[0]}, {p[1]}"


def virtual_screen(root) -> tuple:
    """Прямоугольник всех мониторов (x, y, w, h)."""
    if IS_WIN:
        try:
            u = ctypes.windll.user32
            return (u.GetSystemMetrics(76), u.GetSystemMetrics(77),
                    u.GetSystemMetrics(78), u.GetSystemMetrics(79))
        except Exception:
            pass
    return 0, 0, root.winfo_screenwidth(), root.winfo_screenheight()


def grab_pixel(x: int, y: int):
    """Цвет пикселя экрана (для пипетки)."""
    try:
        try:
            im = ImageGrab.grab(bbox=(x, y, x + 1, y + 1), all_screens=True)
        except TypeError:
            im = ImageGrab.grab(bbox=(x, y, x + 1, y + 1))
        return list(im.convert("RGB").getpixel((0, 0)))
    except Exception:
        return None


class StopDrawing(Exception):
    pass


class Flags:
    """Флаги, общие для интерфейса и потока рисования."""

    def __init__(self):
        self.stop = False
        self.paused = False

    def reset(self):
        self.stop = self.paused = False


# =============================================================================
#  Управление мышью и клавиатурой
# =============================================================================
class Mouse:
    """WinAPI на Windows (быстро и надёжно), pynput на других ОС."""

    def __init__(self):
        self.pressed = False
        if IS_WIN:
            self._u = ctypes.windll.user32
            self._pt = wintypes.POINT()
        else:
            from pynput import mouse as _mouse
            self._m = _mouse.Controller()
            self._btn = _mouse.Button.left

    def move(self, x: float, y: float) -> None:
        x, y = to_px(x), to_px(y)
        if IS_WIN:
            self._u.SetCursorPos(x, y)
        else:
            self._m.position = (x, y)

    def position(self) -> tuple:
        if IS_WIN:
            self._u.GetCursorPos(ctypes.byref(self._pt))
            return self._pt.x, self._pt.y
        x, y = self._m.position
        return int(x), int(y)

    def down(self) -> None:
        if IS_WIN:
            self._u.mouse_event(0x0002, 0, 0, 0, 0)
        else:
            self._m.press(self._btn)
        self.pressed = True

    def up(self) -> None:
        if not self.pressed:
            return
        if IS_WIN:
            self._u.mouse_event(0x0004, 0, 0, 0, 0)
        else:
            self._m.release(self._btn)
        self.pressed = False


class Keys:
    def __init__(self):
        self._k = keyboard.Controller()
        # Ctrl+A по коду клавиши, чтобы работало и на русской раскладке
        self._a = keyboard.KeyCode.from_vk(0x41) if IS_WIN else "a"

    def select_all(self) -> None:
        with self._k.pressed(keyboard.Key.ctrl):
            self._k.tap(self._a)

    def type_text(self, text: str) -> None:
        for ch in text:
            self._k.tap(ch)
            precise_sleep(0.012)

    def tab(self) -> None:
        self._k.tap(keyboard.Key.tab)


# =============================================================================
#  Алгоритмы обработки изображения
# =============================================================================
def prepare_image(img: Image.Image, cfg: dict) -> Image.Image:
    """Прозрачность -> белый фон, затем яркость, контраст и насыщенность."""
    im = img.convert("RGBA")
    im = Image.alpha_composite(Image.new("RGBA", im.size, (255, 255, 255, 255)), im).convert("RGB")
    for enhancer, key in ((ImageEnhance.Brightness, "brightness"), (ImageEnhance.Contrast, "contrast"),
                          (ImageEnhance.Color, "saturation")):
        value = float(cfg[key])
        if abs(value - 1.0) > 0.01:
            im = enhancer(im).enhance(value)
    return im


def nearest_index(arr: np.ndarray, pal: np.ndarray) -> np.ndarray:
    """Ближайший цвет палитры по формуле восприятия 'redmean' (по блокам строк)."""
    out = np.empty(arr.shape[:2], np.int32)
    p = pal[None, None]
    for y0 in range(0, arr.shape[0], 48):
        a = arr[y0:y0 + 48]
        d = a[..., None, :] - p
        rmean = (a[..., 0][..., None] + p[..., 0]) / 2
        dist = ((2 + rmean / 256) * d[..., 0] ** 2 + 4 * d[..., 1] ** 2
                + (2 + (255 - rmean) / 256) * d[..., 2] ** 2)
        out[y0:y0 + 48] = dist.argmin(axis=2)
    return out


def palette_labels(small: Image.Image, rgbs: list, dither: bool) -> np.ndarray:
    """Номер цвета для каждой клетки сетки; -1 означает белый фон."""
    pal = [list(c) for c in rgbs] + [[255, 255, 255]]
    bg = len(pal) - 1
    if dither:
        flat = [v for c in pal for v in c]
        flat += [255, 255, 255] * (256 - len(pal))
        pimg = Image.new("P", (1, 1))
        pimg.putpalette(flat)
        idx = np.asarray(small.quantize(palette=pimg, dither=DITHER_FS), np.int32)
        return np.where(idx >= bg, -1, idx)
    idx = nearest_index(np.asarray(small, np.float32), np.asarray(pal, np.float32))
    return np.where(idx == bg, -1, idx)


def auto_palette(small: Image.Image, count: int, white_thr: int, dither: bool):
    """Подбирает лучшие цвета картинки (median cut + k-means)."""
    count = max(2, min(64, int(count)))
    q = small.quantize(colors=count, method=MEDIANCUT, kmeans=3,
                       dither=DITHER_FS if dither else DITHER_NONE)
    idx = np.asarray(q, np.int32)
    pal = q.getpalette() or []
    colors, remap = [], np.full(256, -1, np.int32)
    for i in np.unique(idx).tolist():
        rgb = [int(v) for v in pal[3 * i:3 * i + 3]]
        if len(rgb) < 3 or min(rgb) >= white_thr:
            continue
        remap[i] = len(colors)
        colors.append({"name": "RGB %d, %d, %d" % tuple(rgb), "rgb": rgb, "pos": None})
    return colors, remap[idx]


def merge_colors(colors: list, labels: np.ndarray, min_share: float = 0.002, min_dist: float = 24.0):
    """Сливает почти одинаковые и слишком редкие цвета: меньше смен цвета, нет «ореолов»."""
    if not colors:
        return colors, labels
    rgb = np.array([c["rgb"] for c in colors], np.float64)
    counts = np.bincount(labels[labels >= 0].ravel(), minlength=len(colors)).astype(np.float64)
    total = max(1.0, counts.sum())
    keep, target = [], {}
    for i in np.argsort(-counts).tolist():
        if counts[i] == 0:
            continue
        if keep:
            dist = np.linalg.norm(rgb[keep] - rgb[i], axis=1)
            j = int(dist.argmin())
            if dist[j] < min_dist or counts[i] / total < min_share:
                target[i] = keep[j]
                continue
        keep.append(i)
    remap = np.full(len(colors) + 1, -1, np.int32)      # последний элемент для -1 (фон)
    for new, old in enumerate(keep):
        remap[old] = new
    for old, kept in target.items():
        remap[old] = remap[kept]
    return [colors[i] for i in keep], remap[labels]


def despeckle(labels: np.ndarray) -> np.ndarray:
    """Убирает одиночные пиксели-шум (фильтр большинства 3×3)."""
    img = Image.fromarray((labels + 1).astype(np.uint8), "L")
    return np.asarray(img.filter(ImageFilter.ModeFilter(3)), np.int32) - 1


def drop_small(labels: np.ndarray, count: int, min_area: int) -> np.ndarray:
    """Убирает пятна меньше min_area клеток (они только тратят время)."""
    if min_area <= 1:
        return labels
    out = labels.copy()
    for i in range(count):
        for comp in components(row_runs(labels == i)):
            if sum(b - a + 1 for _, a, b in comp) < min_area:
                for y, a, b in comp:
                    out[y, a:b + 1] = -1
    return out


def _shift(m: np.ndarray, dy: int, dx: int) -> np.ndarray:
    """out[y, x] = m[y + dy, x + dx], снаружи False."""
    h, w = m.shape
    out = np.zeros_like(m)
    out[max(0, -dy):h - max(0, dy), max(0, -dx):w - max(0, dx)] = \
        m[max(0, dy):h - max(0, -dy), max(0, dx):w - max(0, -dx)]
    return out


_CROSS = ((0, 1), (0, -1), (1, 0), (-1, 0))
_SQUARE = _CROSS + ((1, 1), (1, -1), (-1, 1), (-1, -1))


def morph(m: np.ndarray, radius: int, erode: bool) -> np.ndarray:
    """Эрозия/дилатация почти круглым ядром (чередование креста и квадрата)."""
    out = m.copy()
    for i in range(max(0, int(radius))):
        acc = out.copy()
        for dy, dx in (_SQUARE if i % 2 else _CROSS):
            if erode:
                acc &= _shift(out, dy, dx)
            else:
                acc |= _shift(out, dy, dx)
        out = acc
    return out


def row_runs(mask: np.ndarray) -> list:
    """Непрерывные отрезки True по строкам: [(y, x0, x1), ...]."""
    h, w = mask.shape
    pad = np.zeros((h, w + 2), np.int8)
    pad[:, 1:-1] = mask
    d = np.diff(pad, axis=1)
    ys, xs = np.nonzero(d == 1)
    _, xe = np.nonzero(d == -1)
    return list(zip(ys.tolist(), xs.tolist(), (xe - 1).tolist()))


def count_runs(mask: np.ndarray) -> int:
    return int(np.count_nonzero(np.diff(mask.astype(np.int8), axis=1, prepend=0) == 1))


def components(runs: list) -> list:
    """Связные области (8-связность) из отрезков. Быстро: работает с отрезками, а не пикселями."""
    n = len(runs)
    parent = list(range(n))

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    prev, prev_y, i = [], None, 0
    while i < n:
        y = runs[i][0]
        j = i
        while j < n and runs[j][0] == y:
            j += 1
        if prev_y is not None and y == prev_y + 1:
            p = 0
            for c in range(i, j):
                c0, c1 = runs[c][1], runs[c][2]
                while p < len(prev) and runs[prev[p]][2] < c0 - 1:
                    p += 1
                q = p
                while q < len(prev) and runs[prev[q]][1] <= c1 + 1:
                    ra, rb = find(prev[q]), find(c)
                    if ra != rb:
                        parent[rb] = ra
                    q += 1
        prev, prev_y, i = list(range(i, j)), y, j
    groups = {}
    for k in range(n):
        groups.setdefault(find(k), []).append(runs[k])
    return list(groups.values())


def region_polylines(comp: list, step: int, zigzag: bool, link: int, mark=None) -> list:
    """Штрихи для одной области: строки змейкой, соседние соединяются зигзагом."""
    rows = {}
    for y, a, b in comp:
        rows.setdefault(y, []).append((a, b))
    ys = sorted(rows)
    if step > 1:
        y0, y_last = ys[0], ys[-1]
        ys = [y for y in ys if (y - y0) % step == 0 or y == y_last]
    lines, cur, prev_y, flip = [], None, None, False
    for y in ys:
        segs = sorted(rows[y])
        if flip:
            segs = [(b, a) for a, b in reversed(segs)]
        flip = not flip
        for a, b in segs:
            if mark is not None:
                mark[y, min(a, b):max(a, b) + 1] = True
            if (zigzag and cur is not None and prev_y is not None
                    and 0 < y - prev_y <= step and abs(a - cur[-1][0]) <= link):
                cur.append((a, y))
                if b != a:
                    cur.append((b, y))
            else:
                cur = [(a, y)] if a == b else [(a, y), (b, y)]
                lines.append(cur)
            prev_y = y
    return lines


def order_groups(groups: list, start=(0.0, 0.0)) -> list:
    """Порядок групп штрихов «ближайшая следующая», с разворотом группы при необходимости."""
    groups = [g for g in groups if g]
    n = len(groups)
    if n <= 1:
        return [pl for g in groups for pl in g]
    heads = np.array([g[0][0] for g in groups], np.float64)
    tails = np.array([g[-1][-1] for g in groups], np.float64)
    used = np.zeros(n, bool)
    cur = np.asarray(start, np.float64)
    out = []
    for _ in range(n):
        dh = ((heads - cur) ** 2).sum(1)
        dt = ((tails - cur) ** 2).sum(1)
        dh[used] = np.inf
        dt[used] = np.inf
        ih, it = int(dh.argmin()), int(dt.argmin())
        i, rev = (ih, False) if dh[ih] <= dt[it] else (it, True)
        used[i] = True
        g = [pl[::-1] for pl in groups[i][::-1]] if rev else groups[i]
        out.extend(g)
        cur = np.asarray(g[-1][-1], np.float64)
    return out


def zhang_suen(mask: np.ndarray) -> np.ndarray:
    """Утончение линий до толщины 1 клетка (векторно)."""
    img = mask.astype(np.uint8)
    for _ in range(60):
        changed = False
        for phase in (0, 1):
            P = np.pad(img, 1)
            p2, p3, p4 = P[:-2, 1:-1], P[:-2, 2:], P[1:-1, 2:]
            p5, p6, p7 = P[2:, 2:], P[2:, 1:-1], P[2:, :-2]
            p8, p9 = P[1:-1, :-2], P[:-2, :-2]
            nb = [p2, p3, p4, p5, p6, p7, p8, p9, p2]
            B = sum(x.astype(np.int16) for x in nb[:8])
            A = sum(((nb[k] == 0) & (nb[k + 1] == 1)).astype(np.int16) for k in range(8))
            if phase == 0:
                c = ((p2 * p4 * p6) == 0) & ((p4 * p6 * p8) == 0)
            else:
                c = ((p2 * p4 * p8) == 0) & ((p2 * p6 * p8) == 0)
            kill = (img == 1) & (B >= 2) & (B <= 6) & (A == 1) & c
            if kill.any():
                img[kill] = 0
                changed = True
        if not changed:
            break
    return img.astype(bool)


_N8 = ((0, 1), (1, 0), (0, -1), (-1, 0), (1, 1), (1, -1), (-1, 1), (-1, -1))


def trace_chains(skel: np.ndarray, min_len: int) -> list:
    """Собирает тонкие линии в непрерывные цепочки точек (y, x)."""
    ys, xs = np.nonzero(skel)
    pts = set(zip(ys.tolist(), xs.tolist()))

    def neighbours(p):
        y, x = p
        return [(y + dy, x + dx) for dy, dx in _N8 if (y + dy, x + dx) in pts]

    ends = [p for p in pts if len(neighbours(p)) == 1]
    seen, chains = set(), []
    for start in itertools.chain(ends, sorted(pts)):
        if start in seen:
            continue
        chain, cur, d = [start], start, None
        seen.add(start)
        while True:
            cand = [q for q in neighbours(cur) if q not in seen]
            if not cand:
                break
            if d is None:
                nxt = min(cand, key=lambda q: abs(q[0] - cur[0]) + abs(q[1] - cur[1]))
            else:  # продолжаем в том же направлении, как рука
                nxt = max(cand, key=lambda q: (q[0] - cur[0]) * d[0] + (q[1] - cur[1]) * d[1])
            d = (nxt[0] - cur[0], nxt[1] - cur[1])
            seen.add(nxt)
            chain.append(nxt)
            cur = nxt
        if len(chain) >= min_len:
            if len(chain) > 2:      # стыкуем концы с соседними линиями и замыкаем кольца: никаких щелей
                near_end, near_start = set(chain[-4:]), set(chain[:4])
                tail = [q for q in neighbours(chain[-1]) if q not in near_end]
                head = [q for q in neighbours(chain[0]) if q not in near_start]
                if tail:
                    chain.append(tail[0])
                if head:
                    chain.insert(0, head[0])
            chains.append(chain)
    return chains


def simplify(points: np.ndarray, eps: float) -> np.ndarray:
    """Упрощение ломаной (Рамер-Дуглас-Пекер): убирает «лесенку» пикселей."""
    if len(points) < 3:
        return points
    keep = np.zeros(len(points), bool)
    keep[0] = keep[-1] = True
    stack = [(0, len(points) - 1)]
    while stack:
        a, b = stack.pop()
        if b <= a + 1:
            continue
        seg = points[b] - points[a]
        sub = points[a + 1:b] - points[a]
        length = math.hypot(seg[0], seg[1])
        if length == 0:
            dist = np.hypot(sub[:, 0], sub[:, 1])
        else:
            dist = np.abs(seg[0] * sub[:, 1] - seg[1] * sub[:, 0]) / length
        k = int(dist.argmax())
        if dist[k] > eps:
            m = a + 1 + k
            keep[m] = True
            stack += [(a, m), (m, b)]
    return points[keep]


def densify(points: np.ndarray, max_seg: float) -> np.ndarray:
    """Добавляет точки на длинные отрезки, чтобы сглаживание не срезало углы."""
    if len(points) < 2:
        return points
    out = [points[:1]]
    for a, b in zip(points[:-1], points[1:]):
        n = max(1, int(math.ceil(math.hypot(*(b - a)) / max_seg)))
        t = (np.arange(1, n + 1) / n)[:, None]
        out.append(a + (b - a) * t)
    return np.vstack(out)


def chaikin(points: np.ndarray, iterations: int) -> np.ndarray:
    """Сглаживание углов ломаной с сохранением концов."""
    for _ in range(int(iterations)):
        if len(points) < 3:
            break
        q = 0.75 * points[:-1] + 0.25 * points[1:]
        r = 0.25 * points[:-1] + 0.75 * points[1:]
        mid = np.empty((2 * len(q), 2))
        mid[0::2], mid[1::2] = q, r
        points = np.vstack([points[:1], mid[1:-1], points[-1:]])
    return points


# =============================================================================
#  План рисования
# =============================================================================
@dataclass
class Pass:
    """Один этап рисования: один цвет, одна кисть, список штрихов (ломаных)."""
    title: str
    color: dict
    brush: str      # "thin" | "thick"
    strokes: list   # [np.ndarray (n, 2)] в экранных координатах (для заливки: точки кликов)
    tool: str = "brush"         # "brush" | "fill"
    region_ids: list = None    # для заливки: какие области модели холста закрасятся


class Planner:
    """Превращает картинку в последовательность этапов, как рисовал бы художник:
    набросок контура -> заливка от светлого к тёмному (объект за объектом) -> обводка."""

    GRID_LIMIT = 900

    def __init__(self, cfg: dict):
        self.cfg = cfg
        self.cell = 1.0
        self.origin = (0.0, 0.0)
        self._comp_img = None        # модель областей заливки (для превью)
        self.overlap = min(0.8, max(0.0, cfg["overlap"] / 100))
        self.use_thick = bool(cfg["use_thick"] and cfg["thick_btn"] and cfg["thin_btn"]
                              and cfg["thick_px"] >= cfg["thin_px"] * 1.5)

    # ------------------------------------------------------------------
    def build(self, img: Image.Image, rect):
        cfg = self.cfg
        x1, y1, x2, y2 = [int(v) for v in rect]
        cw, ch = max(4, x2 - x1), max(4, y2 - y1)
        # Шаг сетки = толщина тонкой кисти с учётом перекрытия, поэтому между линиями нет просветов.
        thin = float(cfg["thin_px"])
        cell = max(1.0, min(thin * (1 - self.overlap), thin - 1.0))
        im = prepare_image(img, cfg)
        k = min(cw / cell / im.width, ch / cell / im.height)
        nw, nh = max(1, int(im.width * k)), max(1, int(im.height * k))
        if max(nw, nh) > self.GRID_LIMIT:
            f = self.GRID_LIMIT / max(nw, nh)
            nw, nh = max(1, int(nw * f)), max(1, int(nh * f))
            cell = min(cw / nw, ch / nh)
        small = im.resize((nw, nh), LANCZOS)
        self.cell = cell
        self.origin = (x1 + (cw - nw * cell) / 2 + cell / 2, y1 + (ch - nh * cell) / 2 + cell / 2)

        mode = cfg["mode"]
        want_fill, want_line = mode != MODES[2], mode != MODES[1]
        colors, labels = self._colors(small) if want_fill else ([], None)
        dark = self._dark(colors) if want_line else None
        chains = self._contours(small) if want_line else []

        rect = (x1, y1, x2, y2)
        passes, sketch = [], None
        if want_fill and want_line and cfg["sketch"] and chains:
            sketch = Pass("Набросок контура", dark, "thin", chains)
            passes.append(sketch)
        if want_fill:
            if cfg["despeckle"]:
                labels = despeckle(labels)
            labels = drop_small(labels, len(colors), int(cfg["min_area"]))
            if cfg["use_bucket"]:
                passes += self._bucket_plan(colors, labels, sketch, dark, rect)
            else:
                passes += self._brush_plan(colors, labels)
        if want_line and chains:
            if not want_fill:
                passes.append(Pass("Контур", dark, "thin", chains))
            elif cfg["outline"] or not cfg["sketch"]:
                passes.append(Pass("Обводка контура", dark, "thin", chains))
        return passes, self.render(passes, rect), self.estimate(passes)

    # ------------------------------------------------------------------
    def _colors(self, small):
        cfg = self.cfg
        if cfg["color_src"] == SRC_AUTO:
            colors, labels = auto_palette(small, cfg["auto_colors"], cfg["white_thr"], cfg["dither"])
        else:
            colors = [dict(c) for c in cfg["palette"] if c["on"]]
            if not colors:
                raise ValueError("Включите хотя бы один цвет на вкладке «Цвета»")
            labels = palette_labels(small, [c["rgb"] for c in colors], cfg["dither"])
        if cfg["dither"]:
            return colors, labels               # при дизеринге редкие цвета нужны для переходов
        return merge_colors(colors, labels)

    def _dark(self, colors):
        """Цвет для контура: самый тёмный доступный или чёрный через RGB."""
        cfg = self.cfg
        pool = colors if cfg["color_src"] == SRC_AUTO else [c for c in cfg["palette"] if c["on"]]
        if pool:
            darkest = min(pool, key=lambda c: luminance(c["rgb"]))
            if cfg["color_src"] == SRC_BTN or luminance(darkest["rgb"]) < 70:
                return darkest
        if cfg["color_src"] == SRC_BTN:
            raise ValueError("Для контура включите тёмный цвет в палитре")
        return {"name": "Чёрный", "rgb": [0, 0, 0], "pos": None}

    def _to_screen(self, lines, swap=False):
        ox, oy = self.origin
        out = []
        for pl in lines:
            a = np.asarray(pl, np.float64)
            if swap:
                a = a[:, ::-1]
            out.append(np.column_stack((ox + a[:, 0] * self.cell, oy + a[:, 1] * self.cell)))
        return out

    def _fill(self, mask):
        """Заливка одного цвета: широкая кисть внутри крупных областей, тонкая дорисовывает края."""
        cfg = self.cfg
        vertical = count_runs(mask.T) < count_runs(mask) * 0.85   # направление с меньшим числом штрихов
        m = np.ascontiguousarray(mask.T if vertical else mask)
        thick_lines, rest = [], m
        if self.use_thick:
            radius = float(cfg["thick_px"]) / 2 / self.cell
            step = max(1, int(float(cfg["thick_px"]) * (1 - self.overlap) / self.cell))
            interior = morph(m, int(math.ceil(radius)), erode=True)      # широкая кисть не вылезает за край
            centers = np.zeros_like(m)
            groups = [region_polylines(c, step, cfg["zigzag"], max(2, 2 * step), centers)
                      for c in components(row_runs(interior))]
            thick_lines = order_groups(groups)
            rest = m & ~morph(centers, max(0, int(radius) - 1), erode=False)
        groups = [region_polylines(c, 1, cfg["zigzag"], 4) for c in components(row_runs(rest))]
        thin_lines = order_groups(groups)
        return self._to_screen(thick_lines, vertical), self._to_screen(thin_lines, vertical)

    def _contours(self, small):
        """Контур: градиент Собеля -> утончение -> цепочки -> упрощение и сглаживание."""
        cfg = self.cfg
        a = np.asarray(small.convert("L").filter(ImageFilter.GaussianBlur(0.8)), np.float32)
        p = np.pad(a, 1, mode="edge")
        gx = (p[:-2, 2:] + 2 * p[1:-1, 2:] + p[2:, 2:]) - (p[:-2, :-2] + 2 * p[1:-1, :-2] + p[2:, :-2])
        gy = (p[2:, :-2] + 2 * p[2:, 1:-1] + p[2:, 2:]) - (p[:-2, :-2] + 2 * p[:-2, 1:-1] + p[:-2, 2:])
        edges = np.hypot(gx, gy) / 4 > float(cfg["edge_thr"])
        # две параллельные границы толстой чёрной линии сливаем в одну центральную
        edges = morph(edges, 2 if self.cell < 4 else 1, erode=False)
        chains = trace_chains(zhang_suen(edges), int(cfg["edge_min"]))
        lines = []
        for chain in chains:
            pts = np.asarray(chain, np.float64)[:, ::-1]          # (y, x) -> (x, y)
            pts = densify(simplify(pts, 0.75), 2.5)              # сглаживаем только мелкие изломы
            lines.append(chaikin(pts, int(cfg["smooth"])))
        return self._to_screen(order_groups([[pl] for pl in lines]))

    # ------------------------------------------------------------------
    def _brush_plan(self, colors, labels) -> list:
        """Закрашивание только кистью (если заливка выключена)."""
        passes = []
        for i in sorted(range(len(colors)), key=lambda c: -luminance(colors[c]["rgb"])):
            mask = labels == i
            if not mask.any():
                continue
            thick, thin = self._fill(mask)
            name = colors[i]["name"]
            if thick:
                passes.append(Pass(f"Закраска широкой кистью «{name}»", colors[i], "thick", thick))
            if thin:
                passes.append(Pass(f"Прорисовка «{name}»", colors[i], "thin", thin))
        return passes

    def _bucket_plan(self, colors, labels, sketch, dark, rect) -> list:
        """Заливка ведёрком, как у человека: обводим каждую область её цветом, кликаем
        заливкой и подправляем кистью. Каждый клик заранее проверяется на модели холста:
        если заливка может «утечь» через щель, эта область закрашивается кистью."""
        cfg = self.cfg
        x1, y1, x2, y2 = rect
        width, height = max(1, x2 - x1), max(1, y2 - y1)
        order = sorted(range(len(colors)), key=lambda c: -luminance(colors[c]["rgb"]))
        cols = list(colors)
        if dark is not None and all(c is not dark for c in cols):
            cols.append(dark)
        index = {id(c): k for k, c in enumerate(cols)}

        # 1) граница каждой области её же цветом: замкнутая «стенка» для заливки
        rings = []
        for i in order:
            mask = labels == i
            if not mask.any():
                continue
            edge = mask & ~morph(mask, 1, erode=True)
            lines = [simplify(np.asarray(ch, np.float64)[:, ::-1], 0.5)
                     for ch in trace_chains(zhang_suen(edge), 1)]
            lines = self._to_screen(order_groups([[pl] for pl in lines]))
            if lines:
                rings.append(Pass(f"Контур области «{colors[i]['name']}»", colors[i], "thin", lines))

        # 2) модель холста после всех линий; линии тоньше настоящих = запас надёжности
        sim_w = max(1, int(cfg["thin_px"]) - int(cfg["fill_safety"]))
        canvas = Image.new("L", (width, height), 0)
        draw = ImageDraw.Draw(canvas)
        for p in ([sketch] if sketch else []) + rings:
            self._draw_lines(draw, p.strokes, index[id(p.color)] + 1, sim_w, x1, y1)
        sim = np.asarray(canvas, np.int64) - 1
        light = np.array([math.dist(c["rgb"], (255, 255, 255)) < 60 for c in cols] + [False])
        open_px = ~((sim >= 0) & ~light[sim])           # куда заливка может растечься
        comps = components(row_runs(open_px))
        nc = len(comps)
        comp_img = np.full((height, width), -1, np.int32)
        for cid, comp in enumerate(comps):
            for y, a, b in comp:
                comp_img[y, a:b + 1] = cid
        self._comp_img = comp_img
        fills = []
        if nc:
            # 3) какие области можно безопасно залить одним кликом
            target = self._labels_on_screen(labels, rect)
            inside = comp_img >= 0
            k1 = len(cols) + 1
            hist = np.bincount(comp_img[inside].astype(np.int64) * k1 + target[inside].astype(np.int64) + 1,
                               minlength=nc * k1).reshape(nc, k1)
            area = hist.sum(1)
            dom = hist[:, 1:].argmax(1)
            share = hist[np.arange(nc), dom + 1] / np.maximum(1, area)
            safe = ((area >= int(cfg["min_fill"])) & (share >= 0.95)
                    & (hist[:, 0] <= np.maximum(8, 0.004 * area)))     # не заливаем фон
            # самая «глубокая» точка области: туда кликать безопаснее всего
            depth = np.zeros((height, width), np.int8)
            cur = open_px
            for level in range(1, 7):
                cur = morph(cur, 1, erode=True)
                if not cur.any():
                    break
                depth[cur] = level
            flat_c, flat_d = comp_img.ravel(), depth.ravel()
            idx = np.nonzero(flat_c >= 0)[0]
            srt = idx[np.lexsort((flat_d[idx], flat_c[idx]))]
            best = srt[np.r_[np.nonzero(np.diff(flat_c[srt]))[0], len(srt) - 1]]
            seed = np.zeros(nc, np.int64)
            seed[flat_c[best]] = best
            deep = np.zeros(nc, bool)
            deep[flat_c[best]] = flat_d[best] >= 2
            safe &= deep
            filled = np.full(nc, -1, np.int64)
            for i in order:
                ids = np.nonzero(safe & (dom == i))[0]
                if not len(ids):
                    continue
                clicks = [np.array([[s % width + x1, s // width + y1]], np.float64) for s in seed[ids].tolist()]
                fills.append(Pass(f"Заливка «{colors[i]['name']}»", colors[i], None,
                                  order_groups([[c] for c in clicks]), tool="fill", region_ids=ids.tolist()))
                filled[ids] = i
            painted = np.where(inside, filled[np.maximum(comp_img, 0)], -1)
            sim = np.where(painted >= 0, painted, sim)

        # 4) всё, что не совпало с картинкой, аккуратно подправляем тонкой кистью
        nh, nw = labels.shape
        ox, oy = self.origin
        px = np.clip(np.floor(ox + np.arange(nw) * self.cell + 0.5).astype(np.int64) - x1, 0, width - 1)
        py = np.clip(np.floor(oy + np.arange(nh) * self.cell + 0.5).astype(np.int64) - y1, 0, height - 1)
        need = (labels >= 0) & (sim[np.ix_(py, px)] != labels)
        fixes = []
        for i in order:
            mask = need & (labels == i)
            if not mask.any():
                continue
            groups = [region_polylines(c, 1, cfg["zigzag"], 4) for c in components(row_runs(mask))
                      if sum(b - a + 1 for _, a, b in c) >= 2]
            lines = self._to_screen(order_groups(groups))
            if lines:
                fixes.append(Pass(f"Подправка «{colors[i]['name']}»", colors[i], "thin", lines))
        return rings + fills + fixes

    def _labels_on_screen(self, labels, rect) -> np.ndarray:
        """Номер цвета для каждого экранного пикселя холста (-1 = фон)."""
        x1, y1, x2, y2 = rect
        nh, nw = labels.shape
        ox, oy = self.origin
        c = self.cell
        gx = np.floor((np.arange(x1, x2) + 0.5 - (ox - c / 2)) / c).astype(np.int64)
        gy = np.floor((np.arange(y1, y2) + 0.5 - (oy - c / 2)) / c).astype(np.int64)
        vx = np.nonzero((gx >= 0) & (gx < nw))[0]
        vy = np.nonzero((gy >= 0) & (gy < nh))[0]
        out = np.full((y2 - y1, x2 - x1), -1, np.int32)
        if len(vx) and len(vy):
            out[np.ix_(vy, vx)] = labels[np.ix_(gy[vy], gx[vx])]
        return out

    @staticmethod
    def _draw_lines(draw, lines, fill, width, x1, y1) -> None:
        """Рисует штрихи круглой кистью, округляя координаты так же, как настоящая мышь."""
        w = max(1, to_px(width))
        r = (w - 1) / 2
        for pl in lines:
            pts = [(to_px(x) - x1, to_px(y) - y1) for x, y in pl.tolist()]
            if len(pts) > 1:
                draw.line(pts, fill=fill, width=w, joint="curve")
            for x, y in (pts[0], pts[-1]):
                draw.ellipse((x - r, y - r, x + r, y + r), fill=fill)

    def render(self, passes, rect) -> Image.Image:
        """Точное превью: те же штрихи, кисти и заливки в том же порядке, что и в игре."""
        x1, y1, x2, y2 = rect
        w, h = max(1, x2 - x1), max(1, y2 - y1)
        img = Image.new("RGB", (w, h), "white")
        draw = ImageDraw.Draw(img)
        for p in passes:
            col = tuple(int(v) for v in p.color["rgb"])
            if p.tool == "fill":
                if self._comp_img is not None and p.region_ids:
                    arr = np.array(img)
                    arr[np.isin(self._comp_img, p.region_ids)] = col
                    img = Image.fromarray(arr)
                    draw = ImageDraw.Draw(img)
                continue
            size = self.cfg["thick_px"] if p.brush == "thick" else self.cfg["thin_px"]
            self._draw_lines(draw, p.strokes, col, float(size), x1, y1)
        f = min(1.0, 640 / max(w, h))
        if f < 1:
            img = img.resize((max(1, int(w * f)), max(1, int(h * f))), LANCZOS)
        return img

    def estimate(self, passes) -> dict:
        """Примерное время по той же модели таймингов, что использует Painter."""
        cfg = self.cfg
        timing = Timing(cfg)
        human = cfg["human"] / 100
        if cfg["color_src"] == SRC_BTN:
            switch = cfg["color_pause"] / 1000 + 0.1
        else:
            switch = 2 * cfg["picker_pause"] / 1000 + 1.0
        t, strokes, clicks = 0.0, 0, 0
        last, tool, color = None, None, None
        for p in passes:
            if tuple(p.color["rgb"]) != color:
                t += switch
                color = tuple(p.color["rgb"])
            if p.tool != tool:
                t += cfg["color_pause"] / 1000 + 0.08
                tool = p.tool
            brush = float(cfg["thick_px"] if p.brush == "thick" else cfg["thin_px"])
            for pl in p.strokes:
                if last is not None:
                    t += timing.travel_time(math.hypot(*(pl[0] - last)))
                last = pl[-1]
                if p.tool == "fill":
                    clicks += 1
                    t += 2 * timing.frame + cfg["fill_pause"] / 1000
                    continue
                strokes += 1
                keys = len(timing.key_points(pl, brush))
                length = float(np.hypot(*np.diff(pl, axis=0).T).sum()) if len(pl) > 1 else 0.0
                t += timing.press + timing.release + timing.gap + max(0, keys - 1) * timing.hold
                t += length / timing.speed_px * (1 + 0.25 * human)
        colors = {tuple(p.color["rgb"]) for p in passes}
        # поправка на «живой» разброс пауз (сверено с имитацией рисования)
        t *= 1.0 + 0.3 * human
        return {"strokes": strokes, "clicks": clicks, "colors": len(colors), "seconds": t}

# =============================================================================
#  Тайминги: скорость без артефактов
# =============================================================================
def display_hz() -> float:
    """Частота обновления монитора: браузер обрабатывает движения мыши раз в кадр."""
    if IS_WIN:
        try:
            user32, gdi32 = ctypes.windll.user32, ctypes.windll.gdi32
            hdc = user32.GetDC(0)
            hz = gdi32.GetDeviceCaps(hdc, 116)          # VREFRESH
            user32.ReleaseDC(0, hdc)
            if hz > 1:
                return float(hz)
        except Exception:
            pass
    return 60.0


class Timing:
    """Все паузы рисования считаются от длительности кадра монитора.

    Браузер видит положение мыши раз в кадр и соединяет точки прямыми. Поэтому на каждом
    изломе линии курсор задерживается дольше одного кадра: угол гарантированно попадает
    в игру и не «срезается». Между изломами линия прямая, и там можно двигаться быстро.
    Чем выше частота монитора и точнее таймер ПК, тем быстрее можно рисовать.
    """

    def __init__(self, cfg: dict, hz: float = None):
        level = max(1, min(10, int(cfg.get("speed", 8))))
        t = (level - 1) / 9
        self.level = level
        self.hz = max(30.0, min(360.0, hz or display_hz()))
        f = self.frame = 1.0 / self.hz
        self.hold = f * (4.0 - 2.75 * t)        # угол линии: от 4 до 1.25 кадра
        self.press = f * (3.0 - 1.8 * t)        # после нажатия, до первого движения
        self.release = f * (2.5 - 1.3 * t)      # в конце штриха, до отпускания
        self.gap = f * (3.0 - 2.2 * t)          # пауза между штрихами
        self.step_px = 6 + 54 * t               # длина одного шага курсора
        self.step_dt = f * (1.5 - 0.95 * t)     # время одного шага
        self.speed_px = self.step_px / self.step_dt
        self.travel_speed = self.speed_px * 1.6
        self.priority = 2 if level >= 9 else 1 if level >= 7 else 0

    def travel_time(self, dist: float) -> float:
        return min(0.22, max(self.frame * 0.3, dist / self.travel_speed))

    @staticmethod
    def key_points(pts: np.ndarray, brush_px: float) -> np.ndarray:
        """Изломы линии, которые игра обязана увидеть (всё между ними практически прямое)."""
        if len(pts) <= 2:
            return pts
        return simplify(np.asarray(pts, np.float64), max(0.35, 0.3 * brush_px))


def set_priority(level: int) -> None:
    """0 - обычный, 1 - выше среднего, 2 - высокий (быстрее, но сильнее нагружает ПК)."""
    if not IS_WIN:
        return
    try:
        k32 = ctypes.windll.kernel32
        k32.SetPriorityClass(k32.GetCurrentProcess(), {0: 0x20, 1: 0x8000, 2: 0x80}[level])
        k32.SetThreadPriority(k32.GetCurrentThread(), {0: 0, 1: 1, 2: 2}[level])
    except Exception:
        pass


def measure_pc() -> dict:
    """Быстрый тест ПК (~0.5 с): частота монитора, точность таймера, скорость работы с мышью."""
    hz = display_hz()
    errors = []
    for _ in range(120):
        t0 = time.perf_counter()
        precise_sleep(0.001)
        errors.append(abs(time.perf_counter() - t0 - 0.001))
    errors.sort()
    timer_ms = errors[int(len(errors) * 0.95)] * 1000
    mouse, calls, t0 = Mouse(), 0, time.perf_counter()
    while time.perf_counter() - t0 < 0.12:
        mouse.position()
        calls += 1
    rate = calls / 0.12
    cores = os.cpu_count() or 2
    level = 10 if hz >= 140 else 9 if hz >= 70 else 8
    if timer_ms > 1.0:
        level -= 2
    elif timer_ms > 0.3:
        level -= 1
    if rate < 40000:
        level -= 1
    if cores <= 2:
        level -= 1
    return {"hz": hz, "timer_ms": timer_ms, "rate": rate, "cores": cores, "recommended": max(3, min(10, level))}


# =============================================================================
#  Исполнитель: водит мышью как человек
# =============================================================================
class Painter:
    def __init__(self, cfg: dict, flags: Flags, report):
        self.cfg, self.flags, self.report = cfg, flags, report
        self.mouse, self.keys = Mouse(), Keys()
        self.timing = Timing(cfg)
        self.human = max(0.0, min(1.0, cfg["human"] / 100))
        self.last = None
        self.cur_color = self.cur_brush = self.cur_tool = None

    # ---------------------------------------------------------------- время
    def _more(self, sec: float, spread: float = 0.35) -> float:
        """Живой ритм только в сторону увеличения: безопасный минимум никогда не нарушается."""
        return sec * (1 + self.human * random.uniform(0, spread))

    def _check(self) -> None:
        if self.flags.stop:
            raise StopDrawing("Остановлено")
        if self.flags.paused:
            self.report("status", "Пауза · F9, чтобы продолжить")
            set_priority(0)
            while self.flags.paused and not self.flags.stop:
                time.sleep(0.05)
            if self.flags.stop:
                raise StopDrawing("Остановлено")
            set_priority(self.timing.priority)
            self.report("status", "Продолжаю…")
            color, brush, tool = self.cur_color, self.cur_brush, self.cur_tool
            self.cur_color = self.cur_brush = self.cur_tool = None
            self.last = None
            self.select(color, brush, tool or "brush")    # вдруг во время паузы что-то переключили
        if self.cfg["stop_on_move"] and self.last is not None:
            x, y = self.mouse.position()
            if abs(x - self.last[0]) + abs(y - self.last[1]) > 40:
                raise StopDrawing("Остановлено: мышь сдвинули вручную")

    # ---------------------------------------------------------------- движения
    def _travel(self, x: float, y: float) -> None:
        """Перенос руки с поднятой кистью: плавная дуга с разгоном и торможением."""
        sx, sy = self.last if self.last is not None else self.mouse.position()
        dist = math.hypot(x - sx, y - sy)
        if self.human <= 0.01 or dist < 24:
            self.mouse.move(x, y)
            precise_sleep(self.timing.frame * 0.25)
            return
        duration = self.timing.travel_time(dist) * random.uniform(1.0, 1.3)
        steps = max(4, min(28, int(dist / 35)))
        bend = dist * 0.12 * self.human * random.uniform(-1, 1)
        cx = (sx + x) / 2 - (y - sy) / dist * bend
        cy = (sy + y) / 2 + (x - sx) / dist * bend
        t0 = time.perf_counter()
        for i in range(1, steps + 1):
            t = min_jerk(i / steps)
            u = 1 - t
            self.mouse.move(u * u * sx + 2 * u * t * cx + t * t * x, u * u * sy + 2 * u * t * cy + t * t * y)
            precise_sleep(t0 + duration * i / steps - time.perf_counter())
        self.mouse.move(x, y)

    def click(self, pos, double: bool = False) -> None:
        x, y = pos
        self._travel(x, y)
        precise_sleep(self._more(max(0.03, self.timing.frame * 1.5)))
        for i in range(2 if double else 1):
            self.mouse.down()
            precise_sleep(max(0.016, self.timing.frame))
            self.mouse.up()
            if double and i == 0:
                precise_sleep(0.045)
        self.last = (int(x), int(y))

    def stroke(self, pts: np.ndarray, brush_px: float) -> None:
        """Один штрих. На каждом изломе курсор держится дольше кадра, поэтому даже на максимальной
        скорости игра не срезает углы и не оставляет пробелов. Темп живой: медленнее
        в начале и в конце, как у руки."""
        self._check()
        timing = self.timing
        keys = timing.key_points(pts, brush_px)
        x0, y0 = float(keys[0][0]), float(keys[0][1])
        self._travel(x0, y0)
        precise_sleep(timing.frame * 0.25)
        self.mouse.down()
        precise_sleep(self._more(timing.press))
        if len(keys) == 1:
            end = (x0 + 1, y0)
            self.mouse.move(*end)                    # чтобы игра поставила точку
            precise_sleep(timing.hold)
        else:
            lens = np.hypot(*np.diff(keys, axis=0).T)
            total = max(1e-6, float(lens.sum()))
            done, moves = 0.0, 0
            for (ax, ay), (bx, by), length in zip(keys[:-1].tolist(), keys[1:].tolist(), lens.tolist()):
                n = max(1, int(math.ceil(length / timing.step_px)))
                for k in range(1, n + 1):
                    f = k / n
                    self.mouse.move(ax + (bx - ax) * f, ay + (by - ay) * f)
                    done += length / n
                    edge = min(done, total - done) / total
                    slow = 1 + 1.5 * self.human * max(0.0, 1 - edge / 0.12)
                    precise_sleep(self._more(timing.step_dt * slow, 0.25))
                    moves += 1
                    if moves % 48 == 0 and self.flags.stop:
                        self.mouse.up()
                        raise StopDrawing("Остановлено")
                precise_sleep(self._more(timing.hold, 0.2))     # угол: игра точно его увидит
            end = (float(keys[-1][0]), float(keys[-1][1]))
        precise_sleep(max(0.0, timing.release - timing.hold))
        self.mouse.up()
        self.last = (to_px(end[0]), to_px(end[1]))
        pause = self._more(timing.gap)
        if self.human > 0 and random.random() < 0.012 * self.human:
            pause += random.uniform(0.08, 0.3)          # «присматривается» к рисунку
        precise_sleep(pause)

    def bucket(self, pts) -> None:
        """Один клик заливкой в заранее проверенную точку."""
        self._check()
        self.click((to_px(pts[0][0]), to_px(pts[0][1])))
        precise_sleep(self._more(self.cfg["fill_pause"] / 1000 + self.timing.frame))

    # ---------------------------------------------------------------- инструменты игры
    def set_rgb(self, rgb) -> None:
        """Палитра открывается и закрывается нажатием на одну и ту же кнопку."""
        cfg = self.cfg
        wait = cfg["picker_pause"] / 1000
        self.click(cfg["picker_btn"])
        precise_sleep(wait)
        for key, value in zip(("field_r", "field_g", "field_b"), rgb):
            self.click(cfg[key], double=True)
            precise_sleep(0.05)
            self.keys.select_all()
            precise_sleep(0.03)
            self.keys.type_text(str(int(value)))
            precise_sleep(0.04)
            self.keys.tab()
            precise_sleep(0.05)
        self.click(cfg["picker_btn"])
        precise_sleep(wait)

    @staticmethod
    def _key(color) -> tuple:
        return tuple(color["rgb"]), tuple(color["pos"]) if color.get("pos") else None

    def select(self, color, brush, tool: str = "brush") -> None:
        """Цвет, затем инструмент, затем размер кисти. Лишних нажатий нет."""
        cfg = self.cfg
        pause = cfg["color_pause"] / 1000
        if color is not None and (self.cur_color is None or self._key(color) != self._key(self.cur_color)):
            if cfg["color_src"] == SRC_BTN:
                self.click(color["pos"])
                precise_sleep(self._more(pause))
            else:
                self.set_rgb(color["rgb"])
            self.cur_color = color
        if tool != self.cur_tool:
            btn = cfg["fill_tool"] if tool == "fill" else cfg["brush_tool"]
            if btn:
                self.click(btn)
                precise_sleep(self._more(pause))
            self.cur_tool = tool
        if tool == "brush" and brush and brush != self.cur_brush:
            btn = cfg["thick_btn"] if brush == "thick" else cfg["thin_btn"]
            if btn:
                self.click(btn)
                precise_sleep(self._more(pause))
            self.cur_brush = brush

    # ---------------------------------------------------------------- запуск
    def run(self, passes: list, countdown: int) -> str:
        total = max(1, sum(len(p.strokes) for p in passes))
        done = 0
        set_priority(self.timing.priority)
        try:
            for sec in range(int(countdown), 0, -1):
                if self.flags.stop:
                    raise StopDrawing("Отменено")
                self.report("status", f"Старт через {sec}…  Esc - отмена")
                time.sleep(1)
            for i, p in enumerate(passes, 1):
                self._check()
                self.report("status", f"Этап {i} из {len(passes)} · {p.title}")
                self.select(p.color, p.brush, p.tool)
                brush_px = float(self.cfg["thick_px"] if p.brush == "thick" else self.cfg["thin_px"])
                for pts in p.strokes:
                    if p.tool == "fill":
                        self.bucket(pts)
                    else:
                        self.stroke(pts, brush_px)
                    done += 1
                    if done % 8 == 0:
                        self.report("progress", done / total)
            self.report("progress", 1.0)
            return "Готово! Рисунок завершён"
        except StopDrawing as e:
            return str(e)
        finally:
            self.mouse.up()
            set_priority(0)


# =============================================================================
#  Обновления через GitHub Releases
# =============================================================================
def parse_version(text: str) -> tuple:
    nums = re.findall(r"\d+", text or "")[:4]
    return tuple(int(n) for n in nums) or (0,)


class UpdateCancelled(Exception):
    pass


class Updater:
    """Ищет свежий релиз, скачивает его с проверкой и заменяет программу.

    Релиз на GitHub: тег вида v3.1.0, файлы "AutoDraw Studio.exe" и/или "autodraw.py".
    Для .exe качается .exe, для запуска через Python - .py.
    """

    API = "https://api.github.com/repos/{repo}/releases/latest"
    HEADERS = {"Accept": "application/vnd.github+json", "User-Agent": f"AutoDrawStudio/{APP_VERSION}"}

    def __init__(self, repo: str):
        self.repo = repo.strip().strip("/")

    @property
    def target(self) -> str:
        return sys.executable if FROZEN else os.path.abspath(sys.argv[0])

    def check(self):
        """Информация о новой версии или None, если обновляться не нужно."""
        req = urllib.request.Request(self.API.format(repo=self.repo), headers=self.HEADERS)
        with urllib.request.urlopen(req, timeout=8) as resp:
            data = json.loads(resp.read().decode("utf-8"))
        tag = str(data.get("tag_name") or "")
        if parse_version(tag) <= parse_version(APP_VERSION):
            return None
        ext = ".exe" if FROZEN else ".py"
        asset = next((a for a in data.get("assets") or [] if str(a.get("name", "")).lower().endswith(ext)), None)
        if asset is None:
            return None
        notes = str(data.get("body") or "").strip()
        digest = str(asset.get("digest") or "")
        sha = digest.split(":", 1)[1] if digest.lower().startswith("sha256:") else None
        if not sha:
            m = re.search(r"sha256\W+([0-9a-fA-F]{64})", notes)
            sha = m.group(1) if m else None
        return {"version": tag.lstrip("vV"), "notes": notes, "url": asset["browser_download_url"],
                "size": int(asset.get("size") or 0), "sha256": sha, "name": asset["name"]}

    def download(self, info: dict, progress, cancelled) -> str:
        """Скачивает рядом с программой (или во временную папку) и проверяет целостность."""
        dest = self.target + ".new"
        if not os.access(os.path.dirname(dest), os.W_OK):
            dest = os.path.join(tempfile.gettempdir(), os.path.basename(dest))
        req = urllib.request.Request(info["url"], headers={"User-Agent": self.HEADERS["User-Agent"]})
        digest, done = hashlib.sha256(), 0
        try:
            with urllib.request.urlopen(req, timeout=30) as resp, open(dest, "wb") as out:
                total = int(resp.headers.get("Content-Length") or info["size"] or 0)
                while True:
                    if cancelled():
                        raise UpdateCancelled()
                    chunk = resp.read(1 << 16)
                    if not chunk:
                        break
                    out.write(chunk)
                    digest.update(chunk)
                    done += len(chunk)
                    progress(done, total)
            if total and done != total:
                raise ValueError("файл скачался не полностью")
            if info.get("sha256") and digest.hexdigest().lower() != info["sha256"].lower():
                raise ValueError("контрольная сумма не совпала")
            if FROZEN and done < 1024 * 1024:
                raise ValueError("скачанный файл слишком маленький")
        except BaseException:
            try:
                os.remove(dest)
            except OSError:
                pass
            raise
        return dest

    def install_and_restart(self, new_file: str) -> None:
        """Заменяет старую версию новой и запускает её. После вызова программу нужно закрыть."""
        target = self.target
        if not FROZEN:
            backup = target + ".bak"
            shutil.copy2(target, backup)
            os.replace(new_file, target)
            subprocess.Popen([sys.executable, target] + sys.argv[1:], cwd=APP_DIR)
            return
        # Запущенный .exe нельзя перезаписать, поэтому замену делает маленький скрипт:
        # ждёт, пока программа закроется, удаляет старый файл, ставит новый и запускает его.
        script = os.path.join(tempfile.gettempdir(), f"autodraw_update_{os.getpid()}.bat")
        lines = [
            "@echo off", "chcp 65001 >nul", "setlocal EnableDelayedExpansion", "set tries=0",
            ":wait",
            f'del /f /q "{target}" >nul 2>nul',
            f'if exist "{target}" (',
            "    set /a tries+=1",
            "    if !tries! geq 60 goto fail",
            "    ping -n 2 127.0.0.1 >nul",
            "    goto wait",
            ")",
            f'move /y "{new_file}" "{target}" >nul',
            f'start "" "{target}"',
            'del /f /q "%~f0" >nul 2>nul',
            "exit /b 0",
            ":fail",
            f'del /f /q "{new_file}" >nul 2>nul',
            f'start "" "{target}"',
            'del /f /q "%~f0" >nul 2>nul',
        ]
        with open(script, "w", encoding="utf-8", newline="\r\n") as f:
            f.write("\n".join(lines) + "\n")
        subprocess.Popen(["cmd", "/c", script], creationflags=0x08000000 | 0x00000200, close_fds=True)

    def cleanup(self) -> None:
        """После обновления удаляет старые файлы и остатки незавершённой загрузки."""
        target = self.target
        candidates = [target + ".bak", target + ".new",
                      os.path.join(tempfile.gettempdir(), os.path.basename(target) + ".new")]
        for path in candidates:
            try:
                if os.path.isfile(path):
                    os.remove(path)
            except OSError:
                pass


# =============================================================================
#  Интерфейс: анимации и строительные блоки
# =============================================================================
def ease_out(k: float) -> float:
    return 1 - (1 - k) ** 3


def ease_in_out(k: float) -> float:
    return k * k * (3 - 2 * k)


def ease_out_back(k: float) -> float:
    c = 1.35
    return 1 + (c + 1) * (k - 1) ** 3 + c * (k - 1) ** 2


def _hex_rgb(h: str) -> tuple:
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


def lerp_color(a: str, b: str, k: float) -> str:
    ca, cb = _hex_rgb(a), _hex_rgb(b)
    k = max(0.0, min(1.0, k))
    return "#%02x%02x%02x" % tuple(int(round(x + (y - x) * k)) for x, y in zip(ca, cb))


class Anim:
    """Маленький движок анимаций на after(): твины с плавностью, по одному на ключ."""

    FRAME_MS = 12

    def __init__(self, root):
        self.root = root
        self.jobs = {}

    def tween(self, key, start, end, ms, step, ease=ease_out, done=None):
        self.cancel(key)
        t0 = time.perf_counter()

        def tick():
            k = 1.0 if ms <= 0 else min(1.0, (time.perf_counter() - t0) * 1000 / ms)
            try:
                step(start + (end - start) * ease(k))
            except tk.TclError:                  # виджет уже уничтожен
                self.jobs.pop(key, None)
                return
            if k < 1:
                self.jobs[key] = self.root.after(self.FRAME_MS, tick)
            else:
                self.jobs.pop(key, None)
                if done:
                    done()

        tick()

    def cancel(self, key):
        job = self.jobs.pop(key, None)
        if job is not None:
            try:
                self.root.after_cancel(job)
            except tk.TclError:
                pass


class SoftButton(ctk.CTkButton):
    """Кнопка с плавной сменой цвета при наведении."""

    def __init__(self, master, anim: Anim, color: str, hover: str, **kw):
        kw.setdefault("corner_radius", 10)
        kw.setdefault("height", 36)
        super().__init__(master, fg_color=color, hover=False, **kw)
        self._anim, self._c0, self._c1, self._k = anim, color, hover, 0.0
        self._key = f"btn{id(self)}"
        self.bind("<Enter>", lambda _e: self._fade(1.0), add="+")
        self.bind("<Leave>", lambda _e: self.after(15, self._maybe_leave), add="+")

    def _maybe_leave(self):
        try:
            x, y = self.winfo_pointerxy()
            w = self.winfo_containing(x, y)
        except (tk.TclError, KeyError):
            w = None
        if w is None or not str(w).startswith(str(self)):
            self._fade(0.0)

    def _fade(self, target: float):
        if str(self.cget("state")) == "disabled":
            target = 0.0
        self._anim.tween(self._key, self._k, target, 160, self._paint)

    def _paint(self, k: float):
        self._k = k
        self.configure(fg_color=lerp_color(self._c0, self._c1, k))

    def recolor(self, color: str, hover: str):
        self._c0, self._c1 = color, hover
        self._paint(self._k)


class Section:
    """Карточка настроек: подпись слева, управление справа, тонкие разделители между строками."""

    def __init__(self, app, page, title: str, hint: str = None):
        self.app = app
        ctk.CTkLabel(page, text=title.upper(), font=app.f_cap, text_color=C_FAINT).pack(anchor="w", padx=4, pady=(24, 8))
        self.card = ctk.CTkFrame(page, fg_color=C_SURFACE, corner_radius=14)
        self.card.pack(fill="x")
        self.rows = 0
        if hint:
            ctk.CTkLabel(self.card, text=hint, font=app.f_s, text_color=C_MUTED, wraplength=560,
                         justify="left", anchor="w").pack(anchor="w", padx=18, pady=(14, 12))
            self.rows = 1

    def _separator(self):
        if self.rows:
            ctk.CTkFrame(self.card, height=1, fg_color=C_BORDER).pack(fill="x", padx=18)
        self.rows += 1

    def row(self, title: str, hint: str = None, tight: bool = False):
        self._separator()
        row = ctk.CTkFrame(self.card, fg_color="transparent")
        row.pack(fill="x", padx=18, pady=(13, 6 if tight else 13))
        right = ctk.CTkFrame(row, fg_color="transparent")
        right.pack(side="right", padx=(14, 0))
        left = ctk.CTkFrame(row, fg_color="transparent")
        left.pack(side="left", fill="x", expand=True)
        ctk.CTkLabel(left, text=title, font=self.app.f_b, text_color=C_TEXT, anchor="w").pack(anchor="w")
        if hint:
            ctk.CTkLabel(left, text=hint, font=self.app.f_s, text_color=C_MUTED, anchor="w",
                         justify="left", wraplength=380).pack(anchor="w")
        return row, right

    def block(self):
        """Строка на всю ширину без подписи."""
        self._separator()
        frame = ctk.CTkFrame(self.card, fg_color="transparent")
        frame.pack(fill="x", padx=18, pady=13)
        return frame

    def extra(self):
        """Продолжение предыдущей строки (например, ползунок под подписью)."""
        frame = ctk.CTkFrame(self.card, fg_color="transparent")
        frame.pack(fill="x", padx=18, pady=(0, 14))
        return frame


def place_near(window, app, width: int = None):
    """Ставит окно по центру главного (физические пиксели, без масштабирования CTk)."""
    try:
        window.update_idletasks()
        w, h = window.winfo_width(), window.winfo_height()
        x = app.winfo_rootx() + (app.winfo_width() - w) // 2
        y = app.winfo_rooty() + (app.winfo_height() - h) // 3
        tk.Wm.wm_geometry(window, f"+{max(0, x)}+{max(0, y)}")
    except tk.TclError:
        pass


# =============================================================================
#  Интерфейс: окна
# =============================================================================
class Overlay:
    """Затемнение экрана с перекрестием: выбор точки, области или цвета пипеткой."""

    ALPHA = 0.42

    def __init__(self, root, kind: str, text: str, on_done):
        self.root, self.kind, self.on_done = root, kind, on_done
        self.closed, self.start, self.rect = False, None, None
        x, y, w, h = virtual_screen(root)
        self.ox, self.oy = x, y
        self.top = tk.Toplevel(root)
        self.top.overrideredirect(True)
        self.top.geometry(f"{w}x{h}+{x}+{y}")
        self.top.attributes("-topmost", True)
        self.top.attributes("-alpha", 0.0)
        cv = self.cv = tk.Canvas(self.top, bg="#000000", highlightthickness=0, cursor="crosshair")
        cv.pack(fill="both", expand=True)
        self.hline = cv.create_line(0, 0, w, 0, fill=C_ACCENT, dash=(6, 6))
        self.vline = cv.create_line(0, 0, 0, h, fill=C_ACCENT, dash=(6, 6))
        self.coord = cv.create_text(0, 0, text="", fill="#ffffff", anchor="nw", font=("Segoe UI", 11, "bold"))
        cx, cy = root.winfo_screenwidth() // 2 - x, 96 - y
        cv.create_rectangle(cx - 360, cy - 44, cx + 360, cy + 44, fill=C_SURFACE, outline=C_BORDER, width=1)
        cv.create_text(cx, cy - 11, text=text, fill=C_TEXT, font=("Segoe UI", 16, "bold"))
        cv.create_text(cx, cy + 18, text="Esc или правая кнопка мыши - отмена", fill=C_MUTED,
                       font=("Segoe UI", 11))
        cv.bind("<Motion>", self._motion)
        cv.bind("<ButtonPress-1>", self._down)
        cv.bind("<B1-Motion>", self._drag)
        cv.bind("<ButtonRelease-1>", self._up)
        cv.bind("<Button-3>", lambda e: self.finish(None))
        self.top.bind("<Escape>", lambda e: self.finish(None))
        self.top.after(40, self.top.focus_force)
        root.anim.tween("overlay", 0.0, self.ALPHA, 180, lambda a: self.top.attributes("-alpha", a))

    def _motion(self, e):
        w, h = self.cv.winfo_width(), self.cv.winfo_height()
        self.cv.coords(self.hline, 0, e.y, w, e.y)
        self.cv.coords(self.vline, e.x, 0, e.x, h)
        self.cv.coords(self.coord, e.x + 14, e.y + 12)
        self.cv.itemconfigure(self.coord, text=f"{e.x_root}, {e.y_root}")

    def _down(self, e):
        self.start = (e.x, e.y, e.x_root, e.y_root)

    def _drag(self, e):
        self._motion(e)
        if self.kind != "rect" or not self.start:
            return
        if self.rect is None:
            self.rect = self.cv.create_rectangle(self.start[0], self.start[1], e.x, e.y,
                                                 outline=C_ACCENT_H, width=2, fill="#ffffff")
        else:
            self.cv.coords(self.rect, self.start[0], self.start[1], e.x, e.y)
        self.cv.itemconfigure(self.coord, text=f"{abs(e.x_root - self.start[2])} × {abs(e.y_root - self.start[3])}")

    def _up(self, e):
        if self.kind in ("point", "pixel"):
            self.finish((e.x_root, e.y_root))
            return
        if not self.start:
            return
        x1, y1, x2, y2 = self.start[2], self.start[3], e.x_root, e.y_root
        if abs(x2 - x1) < 12 or abs(y2 - y1) < 12:          # случайный клик вместо выделения
            self.start = None
            if self.rect is not None:
                self.cv.delete(self.rect)
                self.rect = None
            return
        self.finish((min(x1, x2), min(y1, y2), max(x1, x2), max(y1, y2)))

    def finish(self, result):
        if self.closed:
            return
        self.closed = True
        self.root.anim.cancel("overlay")
        self.top.destroy()
        if self.kind == "pixel" and result:
            # сначала убираем затемнение, потом берём цвет пикселя
            self.root.after(160, lambda: self.on_done((result[0], result[1], grab_pixel(*result))))
        else:
            self.root.after(80, self.on_done, result)


class Dialog(ctk.CTkToplevel):
    """Общая основа диалогов: поверх окна, по центру, плавное появление."""

    def __init__(self, app, title: str, size: str):
        super().__init__(app)
        self.app = app
        self.title(title)
        app.set_icon(self)
        self.geometry(size)
        self.resizable(False, False)
        self.configure(fg_color=C_BG)
        self.attributes("-topmost", True)
        self.attributes("-alpha", 0.0)
        self.after(40, self._appear)

    def _appear(self):
        place_near(self, self.app)
        self.app.anim.tween(f"dlg{id(self)}", 0.0, 1.0, 220, lambda a: self.attributes("-alpha", a))
        try:
            self.lift()
            self.focus_force()
        except tk.TclError:
            pass


class ColorDialog(Dialog):
    """Настройка цвета: поля R, G, B, ползунки, HEX и пипетка с экрана."""

    CHANNELS = (("R", "#ff7a7a"), ("G", "#5ee38f"), ("B", "#6fa8ff"))

    def __init__(self, app, color: dict, on_save):
        super().__init__(app, "Цвет", "420x470")
        self.on_save = on_save
        self.name_var = tk.StringVar(value=color["name"])
        self.hex_var = tk.StringVar()
        self.sl_vars = [tk.DoubleVar() for _ in range(3)]
        self.txt_vars = [tk.StringVar() for _ in range(3)]
        self._shown = None

        self.swatch = ctk.CTkFrame(self, height=84, corner_radius=16)
        self.swatch.pack(fill="x", padx=22, pady=(22, 14))
        ctk.CTkEntry(self, textvariable=self.name_var, height=38, font=app.f_b, fg_color=C_SURFACE,
                     border_width=0, corner_radius=10).pack(fill="x", padx=22)
        for i, (ch, col) in enumerate(self.CHANNELS):
            row = ctk.CTkFrame(self, fg_color="transparent")
            row.pack(fill="x", padx=22, pady=(16 if i == 0 else 6, 0))
            ctk.CTkLabel(row, text=ch, width=20, font=app.f_h, text_color=col).pack(side="left")
            ctk.CTkSlider(row, from_=0, to=255, number_of_steps=255, variable=self.sl_vars[i], height=16,
                          progress_color=col, button_color=C_TEXT, button_hover_color="#ffffff", fg_color=C_SURFACE2,
                          command=lambda _v: self._from_sliders()).pack(side="left", fill="x", expand=True, padx=12)
            entry = ctk.CTkEntry(row, textvariable=self.txt_vars[i], width=58, height=32, justify="center",
                                 font=app.f_b, fg_color=C_SURFACE, border_width=0, corner_radius=8)
            entry.pack(side="right")
            entry.bind("<KeyRelease>", lambda _e: self._from_fields())
        row = ctk.CTkFrame(self, fg_color="transparent")
        row.pack(fill="x", padx=22, pady=(18, 0))
        ctk.CTkLabel(row, text="HEX", width=34, font=app.f_s, text_color=C_MUTED).pack(side="left")
        hex_entry = ctk.CTkEntry(row, textvariable=self.hex_var, width=104, height=32, font=app.f_b,
                                 fg_color=C_SURFACE, border_width=0, corner_radius=8)
        hex_entry.pack(side="left", padx=8)
        hex_entry.bind("<KeyRelease>", lambda _e: self._from_hex())
        app.btn(row, "пипетка", self._pipette, width=110, height=32).pack(side="right")
        bar = ctk.CTkFrame(self, fg_color="transparent")
        bar.pack(fill="x", side="bottom", padx=22, pady=22)
        app.btn(bar, "Сохранить", self._save, kind="primary", width=150, height=40).pack(side="right")
        app.btn(bar, "Отмена", self.destroy, width=110, height=40).pack(side="right", padx=8)
        self._set(color["rgb"], animate=False)
        self.after(260, self._grab)

    def _grab(self):
        try:
            self.grab_set()
        except tk.TclError:
            pass

    def _rgb_now(self) -> list:
        return [int(round(v.get())) for v in self.sl_vars]

    def _set(self, rgb, skip: str = "", animate: bool = True):
        rgb = [max(0, min(255, int(v))) for v in rgb]
        for i, v in enumerate(rgb):
            self.sl_vars[i].set(v)
            if skip != "fields":
                self.txt_vars[i].set(str(v))
        if skip != "hex":
            self.hex_var.set(rgb_hex(rgb))
        target = rgb_hex(rgb)
        if animate and self._shown:
            start = self._shown
            self.app.anim.tween(f"sw{id(self)}", 0.0, 1.0, 160,
                                lambda k: self.swatch.configure(fg_color=lerp_color(start, target, k)))
        else:
            self.swatch.configure(fg_color=target)
        self._shown = target

    def _from_sliders(self):
        self._set(self._rgb_now(), animate=False)

    def _from_fields(self):
        try:
            rgb = [int(v.get()) for v in self.txt_vars]
        except ValueError:
            return
        if all(0 <= v <= 255 for v in rgb):
            self._set(rgb, skip="fields")

    def _from_hex(self):
        h = self.hex_var.get().strip().lstrip("#")
        if len(h) == 6:
            try:
                self._set([int(h[i:i + 2], 16) for i in (0, 2, 4)], skip="hex")
            except ValueError:
                pass

    def _pipette(self):
        self.grab_release()
        self.withdraw()

        def done(res):
            if not self.winfo_exists():
                return
            self.deiconify()
            self._grab()
            if res and len(res) == 3 and res[2]:
                self._set(res[2])

        if not self.app.open_overlay("pixel", "Кликните по нужному цвету на экране", done):
            self.deiconify()
            self._grab()

    def _save(self):
        self.on_save({"name": self.name_var.get().strip() or "Цвет", "rgb": self._rgb_now()})
        self.destroy()


class UpdateDialog(Dialog):
    """Предложение обновиться: что нового, загрузка с прогрессом, автоперезапуск."""

    def __init__(self, app, info: dict):
        super().__init__(app, "Обновление", "480x440")
        self.info = info
        self.cancelled = False
        self.busy = False
        self._shown_progress = 0.0
        self.protocol("WM_DELETE_WINDOW", self.later)
        head = ctk.CTkFrame(self, fg_color="transparent")
        head.pack(fill="x", padx=26, pady=(26, 0))
        ctk.CTkLabel(head, text="✦", width=40, height=40, corner_radius=12, fg_color=C_ACCENT_D,
                     text_color=C_ACCENT_H, font=app.f_h).pack(side="left")
        names = ctk.CTkFrame(head, fg_color="transparent")
        names.pack(side="left", padx=14)
        ctk.CTkLabel(names, text="Доступна новая версия", font=app.f_h, text_color=C_TEXT).pack(anchor="w")
        ctk.CTkLabel(names, text=f"{info['version']}  ·  сейчас у вас {APP_VERSION}", font=app.f_s,
                     text_color=C_MUTED).pack(anchor="w")
        box = ctk.CTkTextbox(self, height=170, fg_color=C_SURFACE, corner_radius=12, border_width=0,
                             font=app.f_s, text_color=C_TEXT, wrap="word")
        box.pack(fill="both", expand=True, padx=26, pady=(20, 12))
        box.insert("0.0", info["notes"] or "Улучшения и исправления.")
        box.configure(state="disabled")
        self.bar = ctk.CTkProgressBar(self, height=6, corner_radius=3, fg_color=C_SURFACE2, progress_color=C_ACCENT)
        self.bar.set(0)
        self.status = ctk.CTkLabel(self, text="Программа скачает обновление, заменит старые файлы и перезапустится.",
                                   font=app.f_s, text_color=C_MUTED, anchor="w", justify="left", wraplength=420)
        self.status.pack(fill="x", padx=26)
        bar = ctk.CTkFrame(self, fg_color="transparent")
        bar.pack(fill="x", side="bottom", padx=26, pady=24)
        self.b_update = app.btn(bar, "Обновить", self.start, kind="primary", width=150, height=40)
        self.b_update.pack(side="right")
        self.b_later = app.btn(bar, "Позже", self.later, width=96, height=40)
        self.b_later.pack(side="right", padx=8)
        self.b_skip = app.btn(bar, "Пропустить", self.skip, kind="flat", width=110, height=40)
        self.b_skip.pack(side="left")

    def start(self):
        if self.busy:
            return
        self.busy = True
        self.cancelled = False
        for b in (self.b_update, self.b_skip):
            b.configure(state="disabled")
        self.b_later.configure(text="Отмена")
        self.bar.pack(fill="x", padx=26, pady=(0, 10), before=self.status)
        self.status.configure(text="Скачиваю…", text_color=C_MUTED)
        self.app.download_update(self.info)

    def on_progress(self, done: int, total: int):
        value = done / total if total else 0.0
        start = self._shown_progress
        self._shown_progress = value
        self.app.anim.tween(f"upbar{id(self)}", start, value, 200, self.bar.set)
        size = f"{done / 1e6:.1f} из {total / 1e6:.1f} МБ" if total else f"{done / 1e6:.1f} МБ"
        self.status.configure(text=f"Скачиваю…  {size}")

    def on_error(self, text: str):
        self.busy = False
        for b in (self.b_update, self.b_skip):
            b.configure(state="normal")
        self.b_later.configure(text="Позже")
        self.status.configure(text=text, text_color=C_BAD)

    def on_ready(self):
        self.b_later.configure(state="disabled")
        self.status.configure(text="Устанавливаю и перезапускаю…", text_color=C_OK)

    def later(self):
        self.cancelled = True
        self.destroy()

    def skip(self):
        self.app.cfg["skip_version"] = self.info["version"]
        self.app.save()
        self.destroy()


# =============================================================================
#  Главное окно
# =============================================================================
class App(ctk.CTk):
    PREVIEW_SIZE = (320, 216)

    def __init__(self):
        super().__init__()
        self.cfg = load_settings()
        self.flags = Flags()
        self.q: queue.Queue = queue.Queue()
        self.anim = Anim(self)
        self.updater = Updater(self.cfg.get("update_repo") or UPDATE_REPO)
        self.update_info = None
        self.upd_dialog = None
        self.pc = None
        self.image = None
        self.previews = {"Результат": None, "Оригинал": None}
        self._pv_shown = None
        self.busy = False
        self.overlay = None
        self.dialog = None
        self.current_page = None
        self._preview_job = None
        self._plan_token = 0
        self._setters, self.vars, self.pos_labels = {}, {}, {}
        self._stats = {"strokes": 0.0, "clicks": 0.0, "seconds": 0.0}
        self._progress = 0.0
        self._toast_frame = None
        self._ind_y = None

        self.title(APP_NAME)
        self.set_icon()
        self.geometry("1260x820")
        self.minsize(1140, 720)
        self.configure(fg_color=C_BG)
        self.attributes("-topmost", bool(self.cfg["topmost"]))
        self.attributes("-alpha", 0.0)
        self._init_fonts()
        self.grid_columnconfigure(1, weight=1)
        self.grid_rowconfigure(0, weight=1)
        self._build_sidebar()
        self._build_pages()
        self._build_right_panel()
        self.show_page(PAGES[0][0])

        self.bind_all("<Control-KeyPress>", self._on_ctrl)
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        self.listener = keyboard.Listener(on_press=self._on_hotkey)
        self.listener.daemon = True
        self.listener.start()
        self.after(40, self._poll)
        self.after(60, lambda: self.anim.tween("window", 0.0, 1.0, 360, lambda a: self.attributes("-alpha", a)))
        self.after(700, self._startup_tasks)

    # ------------------------------------------------------------ основа
    def _init_fonts(self):
        families = set(tkfont.families(self))

        def pick(*names):
            return next((n for n in names if n in families), "TkDefaultFont")

        display = pick("Segoe UI Variable Display", "Segoe UI", "Inter", "Helvetica Neue", "Arial")
        text = pick("Segoe UI Variable Text", "Segoe UI", "Inter", "Helvetica Neue", "Arial")
        font = ctk.CTkFont
        self.f_title = font(family=display, size=26, weight="bold")
        self.f_h = font(family=display, size=16, weight="bold")
        self.f_b = font(family=text, size=13)
        self.f_s = font(family=text, size=12)
        self.f_cap = font(family=text, size=11, weight="bold")
        self.f_num = font(family=display, size=21, weight="bold")
        self.f_btn = font(family=text, size=14, weight="bold")
        self.f_icon = font(family=text, size=15)

    def btn(self, parent, text, command, kind: str = "ghost", **kw):
        """Кнопки четырёх видов: primary, ghost, flat, danger."""
        base, hover, fg = {
            "primary": (C_ACCENT, C_ACCENT_H, "#ffffff"),
            "ghost": (C_SURFACE2, C_HOVER, C_TEXT),
            "flat": (C_SURFACE, C_SURFACE2, C_MUTED),
            "danger": (C_SURFACE2, "#3b2027", C_BAD),
        }[kind]
        kw.setdefault("font", self.f_btn if kind == "primary" else self.f_b)
        return SoftButton(parent, self.anim, base, hover, text=text, command=command, text_color=fg,
                          text_color_disabled=C_FAINT, **kw)

    def set_icon(self, window=None):
        """customtkinter ставит свою иконку через ~200 мс, поэтому свою задаём чуть позже."""
        win = window or self

        def apply():
            try:
                if os.path.exists(ICON_PATH) and win.winfo_exists():
                    win.iconbitmap(ICON_PATH)
            except tk.TclError:
                pass

        win.after(300, apply)

    def toast(self, text: str, kind: str = "info"):
        """Ненавязчивое уведомление внизу окна: выезжает и прячется само."""
        if self._toast_frame is not None:
            try:
                self._toast_frame.destroy()
            except tk.TclError:
                pass
        dot = {"ok": C_OK, "warn": C_WARN, "bad": C_BAD}.get(kind, C_ACCENT)
        frame = ctk.CTkFrame(self, fg_color=C_SURFACE2, corner_radius=14, border_width=1, border_color=C_BORDER)
        ctk.CTkLabel(frame, text="●", font=self.f_s, text_color=dot).pack(side="left", padx=(16, 8), pady=12)
        ctk.CTkLabel(frame, text=text, font=self.f_b, text_color=C_TEXT, wraplength=460,
                     justify="left").pack(side="left", padx=(0, 18), pady=12)
        self._toast_frame = frame
        frame.place(relx=0.5, rely=1.12, anchor="s")
        frame.lift()
        move = lambda v: frame.place_configure(rely=v)
        self.anim.tween("toast", 1.12, 0.975, 380, move, ease=ease_out_back)

        def hide():
            if self._toast_frame is frame:
                self.anim.tween("toast", 0.975, 1.12, 260, move, ease=ease_in_out,
                                done=lambda: frame.destroy() if frame.winfo_exists() else None)
        self.after(3200 + 25 * len(text), hide)

    # ------------------------------------------------------------ каркас
    def _build_sidebar(self):
        side = self.side = ctk.CTkFrame(self, width=220, corner_radius=0, fg_color=C_SIDE)
        side.grid(row=0, column=0, sticky="nsw")
        side.pack_propagate(False)
        logo = ctk.CTkFrame(side, fg_color="transparent")
        logo.pack(fill="x", padx=20, pady=(28, 30))
        self._logo = None
        try:
            if os.path.exists(ICON_PATH):
                icon = Image.open(ICON_PATH).convert("RGBA")
                self._logo = ctk.CTkImage(light_image=icon, dark_image=icon, size=(34, 34))
        except Exception:
            self._logo = None
        if self._logo is not None:
            ctk.CTkLabel(logo, text="", image=self._logo).pack(side="left")
        else:
            ctk.CTkLabel(logo, text="✦", width=34, height=34, corner_radius=10, fg_color=C_ACCENT,
                         text_color="#ffffff", font=self.f_h).pack(side="left")
        names = ctk.CTkFrame(logo, fg_color="transparent")
        names.pack(side="left", padx=12)
        ctk.CTkLabel(names, text="AutoDraw", font=self.f_h, text_color=C_TEXT).pack(anchor="w")
        ctk.CTkLabel(names, text="Studio", font=self.f_s, text_color=C_FAINT).pack(anchor="w")
        self.nav = {}
        for name, icon in PAGES:
            b = SoftButton(side, self.anim, C_SIDE, C_SURFACE, text=f"{icon}    {name}", anchor="w", height=40,
                           font=self.f_b, text_color=C_MUTED, command=lambda n=name: self.show_page(n))
            b.pack(fill="x", padx=12, pady=2)
            self.nav[name] = b
        scale = ctk.ScalingTracker.get_window_scaling(self)
        self.nav_ind = tk.Frame(side, bg=C_ACCENT, width=max(2, int(3 * scale)), height=int(18 * scale))
        bottom = ctk.CTkFrame(side, fg_color="transparent")
        bottom.pack(side="bottom", fill="x", padx=18, pady=20)
        self.upd_badge = SoftButton(bottom, self.anim, C_ACCENT_D, "#2f2852", text="✦  Доступно обновление",
                                    text_color=C_ACCENT_H, font=self.f_s, height=34, command=self._open_update)
        self.vars["topmost"] = tk.BooleanVar(value=bool(self.cfg["topmost"]))
        row = ctk.CTkFrame(bottom, fg_color="transparent")
        row.pack(fill="x", pady=(12, 0))
        ctk.CTkLabel(row, text="Поверх окон", font=self.f_s, text_color=C_MUTED).pack(side="left")
        ctk.CTkSwitch(row, text="", width=40, switch_width=36, switch_height=20, variable=self.vars["topmost"],
                      command=self._apply_topmost, progress_color=C_ACCENT, fg_color=C_SURFACE2,
                      button_color="#ffffff", button_hover_color="#ffffff").pack(side="right")
        ctk.CTkLabel(bottom, text=f"версия {APP_VERSION}", font=self.f_s, text_color=C_FAINT).pack(anchor="w", pady=(10, 0))
        self._badge_anchor = row

    def _build_pages(self):
        holder = ctk.CTkFrame(self, fg_color=C_BG, corner_radius=0)
        holder.grid(row=0, column=1, sticky="nsew")
        self.pages = {}
        builders = (self._page_image, self._page_calibration, self._page_colors,
                    self._page_style, self._page_speed, self._page_about)
        for (name, _icon), build in zip(PAGES, builders):
            page = ctk.CTkScrollableFrame(holder, fg_color=C_BG, corner_radius=0,
                                          scrollbar_button_color=C_SURFACE2, scrollbar_button_hover_color=C_HOVER)
            body = ctk.CTkFrame(page, fg_color="transparent")
            body.pack(fill="x", padx=(34, 22), pady=(30, 36))
            self.pages[name] = page
            build(body)

    def show_page(self, name: str):
        if name == self.current_page:
            return
        old = self.pages.get(self.current_page)
        if old is not None:
            old.place_forget()
        page = self.pages[name]
        first = self.current_page is None
        self.current_page = name

        def place(v):
            page.place(relx=v, rely=0, relwidth=1, relheight=1)

        if first:
            place(0)
        else:
            place(0.035)
            self.anim.tween("page", 0.035, 0.0, 320, place)
        for n, b in self.nav.items():
            active = n == name
            b.recolor(C_SURFACE if active else C_SIDE, C_SURFACE)
            b.configure(text_color=C_TEXT if active else C_MUTED)
        self.after(30 if first else 0, lambda: self._move_indicator(name, not first))

    def _move_indicator(self, name: str, animate: bool):
        b = self.nav[name]
        try:
            self.side.update_idletasks()
            y = b.winfo_y() + (b.winfo_height() - self.nav_ind.winfo_reqheight()) // 2
            x = b.winfo_x() + int(6 * ctk.ScalingTracker.get_window_scaling(self))
        except tk.TclError:
            return
        if animate and self._ind_y is not None:
            start = self._ind_y
            self.anim.tween("nav", start, y, 300, lambda v: self.nav_ind.place(x=x, y=int(v)))
        else:
            self.nav_ind.place(x=x, y=y)
        self.nav_ind.lift()
        self._ind_y = y

    def _build_right_panel(self):
        panel = ctk.CTkFrame(self, width=384, corner_radius=0, fg_color=C_SIDE)
        panel.grid(row=0, column=2, sticky="nse")
        panel.pack_propagate(False)
        head = ctk.CTkFrame(panel, fg_color="transparent")
        head.pack(fill="x", padx=24, pady=(28, 12))
        ctk.CTkLabel(head, text="Превью", font=self.f_h, text_color=C_TEXT).pack(side="left")
        self.vars["pv"] = tk.StringVar(value="Результат")
        ctk.CTkSegmentedButton(head, values=["Результат", "Оригинал"], variable=self.vars["pv"],
                               command=lambda _v: self._show_preview(), font=self.f_s, height=28, corner_radius=8,
                               fg_color=C_SURFACE2, selected_color=C_HOVER, selected_hover_color=C_HOVER,
                               unselected_color=C_SURFACE2, unselected_hover_color=C_HOVER,
                               text_color=C_TEXT).pack(side="right")
        frame = ctk.CTkFrame(panel, width=336, height=232, fg_color=C_SURFACE, corner_radius=16)
        frame.pack(padx=24)
        frame.pack_propagate(False)
        self.pv_label = ctk.CTkLabel(frame, text="Откройте картинку\nили нажмите Ctrl+V",
                                     font=self.f_b, text_color=C_FAINT)
        self.pv_label.pack(expand=True, fill="both", padx=8, pady=8)

        stats = ctk.CTkFrame(panel, fg_color="transparent")
        stats.pack(fill="x", padx=24, pady=(18, 0))
        self.stat_labels = {}
        for i, (key, title) in enumerate((("strokes", "штрихов"), ("clicks", "заливок"), ("seconds", "время"))):
            stats.grid_columnconfigure(i, weight=1, uniform="s")
            cell = ctk.CTkFrame(stats, fg_color="transparent")
            cell.grid(row=0, column=i, sticky="w")
            value = ctk.CTkLabel(cell, text="–", font=self.f_num, text_color=C_TEXT)
            value.pack(anchor="w")
            ctk.CTkLabel(cell, text=title, font=self.f_s, text_color=C_FAINT).pack(anchor="w")
            self.stat_labels[key] = value

        ctk.CTkLabel(panel, text="ПЛАН", font=self.f_cap, text_color=C_FAINT).pack(anchor="w", padx=26, pady=(22, 6))
        self.plan_label = ctk.CTkLabel(panel, text="появится после загрузки картинки", font=self.f_s,
                                       text_color=C_MUTED, justify="left", anchor="w")
        self.plan_label.pack(fill="x", padx=26)
        ctk.CTkFrame(panel, fg_color="transparent").pack(fill="both", expand=True)

        self.ready_label = ctk.CTkLabel(panel, text="", font=self.f_s, justify="left", anchor="w", wraplength=330)
        self.ready_label.pack(fill="x", padx=26, pady=(0, 12))
        line = ctk.CTkFrame(panel, fg_color="transparent")
        line.pack(fill="x", padx=26)
        self.dot = ctk.CTkLabel(line, text="●", font=self.f_s, text_color=C_FAINT)
        self.dot.pack(side="left")
        self.status = ctk.CTkLabel(line, text="Готов к работе", font=self.f_s, text_color=C_MUTED,
                                   anchor="w", justify="left", wraplength=300)
        self.status.pack(side="left", padx=8, fill="x")
        self.progress = ctk.CTkProgressBar(panel, height=4, corner_radius=2, fg_color=C_SURFACE2, progress_color=C_ACCENT)
        self.progress.set(0)
        self.progress.pack(fill="x", padx=24, pady=(10, 14))
        self.btn_draw = self.btn(panel, "Нарисовать", self.start, kind="primary", height=52, corner_radius=14)
        self.btn_draw.pack(fill="x", padx=24)
        row = ctk.CTkFrame(panel, fg_color="transparent")
        row.pack(fill="x", padx=24, pady=(8, 26))
        self.btn(row, "Пауза  F9", self.toggle_pause, height=40).pack(side="left", expand=True, fill="x", padx=(0, 4))
        self.btn(row, "Стоп  Esc", self.stop, kind="danger", height=40).pack(side="left", expand=True, fill="x", padx=(4, 0))
        self._update_ready()


    # ------------------------------------------------------------ элементы управления
    def _header(self, body, title: str, subtitle: str):
        ctk.CTkLabel(body, text=title, font=self.f_title, text_color=C_TEXT).pack(anchor="w")
        ctk.CTkLabel(body, text=subtitle, font=self.f_b, text_color=C_MUTED, wraplength=600,
                     justify="left", anchor="w").pack(anchor="w", pady=(6, 0))

    def _slider(self, sec: Section, key, title, lo, hi, step, fmt="{:.0f}", suffix="", hint=None,
                caption=None, on_change=None):
        is_int = isinstance(DEFAULTS[key], int) and not isinstance(DEFAULTS[key], bool)
        var = tk.DoubleVar(value=float(self.cfg[key]))
        self.vars[key] = var
        _row, right = sec.row(title, hint, tight=True)
        value = ctk.CTkLabel(right, text="", font=self.f_b, text_color=C_ACCENT_H)
        value.pack()
        holder = sec.extra()

        def show(v):
            value.configure(text=caption(v) if caption else fmt.format(v) + suffix)

        def changed(_v=None, user=True):
            v = var.get()
            v = int(round(v)) if is_int else round(v, 2)
            self.cfg[key] = v
            show(v)
            if on_change:
                on_change(v, user)
            self.schedule_preview()

        ctk.CTkSlider(holder, from_=lo, to=hi, number_of_steps=max(1, int(round((hi - lo) / step))),
                      variable=var, command=changed, height=16, fg_color=C_SURFACE2, progress_color=C_ACCENT,
                      button_color=C_TEXT, button_hover_color="#ffffff").pack(fill="x")
        show(self.cfg[key])
        self._setters[key] = lambda v: (var.set(v), changed(None, False))
        return value

    def _switch(self, sec: Section, key, title, hint=None, on_change=None):
        _row, right = sec.row(title, hint)
        var = tk.BooleanVar(value=bool(self.cfg[key]))
        self.vars[key] = var

        def changed():
            self.cfg[key] = bool(var.get())
            if on_change:
                on_change(self.cfg[key])
            self.schedule_preview()

        ctk.CTkSwitch(right, text="", width=44, switch_width=40, switch_height=22, variable=var, command=changed,
                      progress_color=C_ACCENT, fg_color=C_SURFACE2, button_color="#ffffff",
                      button_hover_color="#ffffff").pack()

    def _segmented(self, parent, key, values, on_change=None):
        var = tk.StringVar(value=self.cfg[key])
        self.vars[key] = var

        def changed(value):
            self.cfg[key] = value
            if on_change:
                on_change(value)
            self.schedule_preview()

        ctk.CTkSegmentedButton(parent, values=values, variable=var, command=changed, font=self.f_b, height=36,
                               corner_radius=10, fg_color=C_SURFACE2, selected_color=C_ACCENT,
                               selected_hover_color=C_ACCENT_H, unselected_color=C_SURFACE2,
                               unselected_hover_color=C_HOVER, text_color=C_TEXT).pack(fill="x")

    def _pick(self, sec: Section, key, title, hint, kind="point"):
        _row, right = sec.row(title, hint)
        chip = ctk.CTkLabel(right, text="", font=self.f_s, corner_radius=8, width=112, height=30)
        chip.pack(side="left", padx=(0, 8))
        self.btn(right, "Указать", lambda: self._pick_point(key, title, kind), kind="primary",
                 width=92, height=30, font=self.f_b).pack(side="left")
        self.btn(right, "✕", lambda: self._clear_point(key), width=30, height=30).pack(side="left", padx=(6, 0))
        self.pos_labels[key] = chip
        self._refresh_pos(key, flash=False)

    def _refresh_pos(self, key, flash: bool = True):
        chip = self.pos_labels.get(key)
        if chip is not None:
            p = self.cfg[key]
            target = "#14261b" if p else C_SURFACE2
            chip.configure(text=("✓  " + fmt_pos(p)) if p else "не задано",
                           text_color=C_OK if p else C_FAINT, fg_color=target)
            if flash and p:
                self.anim.tween(f"chip{key}", 0.0, 1.0, 700,
                                lambda k: chip.configure(fg_color=lerp_color(C_ACCENT, target, k)))
        self._update_ready()

    # ------------------------------------------------------------ страницы
    def _page_image(self, body):
        self._header(body, "Рисунок", "Откройте картинку, и программа нарисует её в игре как человек: "
                                "набросок, заливка цветом, детали и обводка.")
        drop = ctk.CTkFrame(body, fg_color=C_SURFACE, corner_radius=16)
        drop.pack(fill="x", pady=(24, 0))
        inner = ctk.CTkFrame(drop, fg_color="transparent")
        inner.pack(fill="x", padx=22, pady=22)
        ctk.CTkLabel(inner, text="◐", width=52, height=52, corner_radius=14, fg_color=C_ACCENT_D,
                     text_color=C_ACCENT_H, font=self.f_title).pack(side="left")
        text = ctk.CTkFrame(inner, fg_color="transparent")
        text.pack(side="left", padx=16, fill="x", expand=True)
        ctk.CTkLabel(text, text="Выберите картинку", font=self.f_h, text_color=C_TEXT).pack(anchor="w")
        self.img_info = ctk.CTkLabel(text, text="PNG, JPG, WEBP или Ctrl+V из буфера обмена",
                                     font=self.f_s, text_color=C_MUTED)
        self.img_info.pack(anchor="w")
        self.btn(inner, "Вставить", self.paste, width=96, height=38).pack(side="right")
        self.btn(inner, "Открыть", self.open_file, kind="primary", width=110, height=38,
                 font=self.f_b).pack(side="right", padx=8)
        sec = Section(self, body, "Что рисовать")
        self._segmented(sec.block(), "mode", MODES)
        sec = Section(self, body, "Обработка")
        self._slider(sec, "brightness", "Яркость", 0.5, 1.5, 0.05, "{:.2f}")
        self._slider(sec, "contrast", "Контраст", 0.5, 2.0, 0.05, "{:.2f}")
        self._slider(sec, "saturation", "Насыщенность", 0.0, 2.0, 0.05, "{:.2f}")
        self._switch(sec, "despeckle", "Убирать шум", "Сглаживает одиночные точки и мелкие пятна")
        self._slider(sec, "min_area", "Мелкие пятна", 1, 60, 1, suffix=" кл.",
                     hint="Пятна меньше этого размера не рисуются")

    def _page_calibration(self, body):
        self._header(body, "Калибровка", "Покажите, где в игре холст, палитра и инструменты. Нажмите «Указать», "
                                     "экран затемнится, и кликните по нужному месту. Всё сохраняется само.")
        sec = Section(self, body, "Холст")
        self._pick(sec, "canvas", "Область рисования", "Выделите мышкой весь холст игры", "rect")
        sec = Section(self, body, "Палитра RGB", "Программа нажимает на палитру, вписывает R, G, B и "
                                                     "нажимает на неё ещё раз, чтобы закрыть.")
        self._pick(sec, "picker_btn", "Кнопка палитры", "Открывает и закрывает окно с полями R, G, B")
        self._pick(sec, "field_r", "Поле R", "Сначала откройте палитру в игре")
        self._pick(sec, "field_g", "Поле G", "Зелёный канал")
        self._pick(sec, "field_b", "Поле B", "Синий канал")
        _row, right = sec.row("Проверка палитры", "В игре должен выбраться красный цвет")
        self.btn(right, "Тест", self.test_rgb, width=92, height=30).pack()
        sec = Section(self, body, "Инструменты")
        self._pick(sec, "brush_tool", "Кисть", "Карандаш или кисть на панели инструментов")
        self._pick(sec, "fill_tool", "Заливка", "Ведёрко с краской")
        sec = Section(self, body, "Размер кисти")
        self._pick(sec, "thin_btn", "Тонкая", "Для контуров и деталей")
        self._pick(sec, "thick_btn", "Широкая", "Необязательно, нужна если заливка выключена")
        sec = Section(self, body, "Проверка")
        _row, right = sec.row("Показать все точки", "Курсор по очереди пройдёт по всем указанным местам")
        self.btn(right, "Показать", self.test_points, width=104, height=30).pack()

    def _page_colors(self, body):
        self._header(body, "Цвета", "Как программа будет набирать цвета в игре.")
        sec = Section(self, body, "Источник цветов")
        block = sec.block()
        self._segmented(block, "color_src", SOURCES, on_change=self._on_source)
        self.src_hint = ctk.CTkLabel(block, text="", font=self.f_s, text_color=C_MUTED, wraplength=560,
                                     justify="left", anchor="w")
        self.src_hint.pack(anchor="w", pady=(10, 0))
        sec = Section(self, body, "Авто-подбор")
        self._slider(sec, "auto_colors", "Количество цветов", 2, 48, 1,
                     hint="Больше цветов: точнее, но дольше (каждый цвет ≈ 1 с)")
        self._slider(sec, "white_thr", "Порог белого фона", 200, 255, 1, hint="Всё светлее считается фоном")
        self._switch(sec, "dither", "Дизеринг", "Плавные переходы точками, дольше рисуется")
        sec = Section(self, body, "Мои цвета", "Нажмите на квадрат, чтобы задать точный цвет (RGB, HEX или пипетка). "
                                               "◎ указывает, где кнопка этого цвета в игре.")
        block = sec.block()
        self.pal_box = ctk.CTkFrame(block, fg_color="transparent")
        self.pal_box.pack(fill="x")
        self.btn(block, "＋  Добавить цвет", self._add_color, height=34).pack(anchor="w", pady=(10, 0))
        self._build_palette()
        self._on_source(self.cfg["color_src"])

    def _page_style(self, body):
        self._header(body, "Стиль", "Как программа водит кистью. Расстояние между линиями считается от толщины кисти, "
                                "поэтому промежутков нет даже у самой тонкой.")
        sec = Section(self, body, "Кисти")
        self._slider(sec, "thin_px", "Тонкая кисть", 1, 30, 1, suffix=" px", hint="Реальная толщина линии в игре")
        self._slider(sec, "thick_px", "Широкая кисть", 4, 80, 1, suffix=" px")
        self._slider(sec, "overlap", "Перекрытие линий", 0, 60, 1, suffix=" %", hint="Больше = плотнее закраска")
        self._switch(sec, "use_thick", "Закрашивать широкой кистью", "Когда заливка выключена")
        sec = Section(self, body, "Заливка", "Программа обводит каждую область её цветом и заливает одним кликом. "
                                                "Каждый клик сначала проверяется на модели холста: если через щель краска "
                                                "может утечь, область закрашивается кистью. Холст перед стартом должен быть чистым.")
        self._switch(sec, "use_bucket", "Использовать заливку", "Лучше всего с тонкой кистью от 3 px")
        self._slider(sec, "fill_safety", "Запас надёжности", 0, 3, 1, suffix=" px", hint="Больше = осторожнее")
        self._slider(sec, "min_fill", "Минимальная площадь", 20, 2000, 10, suffix=" px²",
                     hint="Области меньше закрашиваются кистью")
        sec = Section(self, body, "Как человек")
        self._switch(sec, "sketch", "Сначала набросок", "Тёмный контур до заливки")
        self._switch(sec, "outline", "Обвести в конце", "Чёткий контур поверх цвета")
        self._switch(sec, "zigzag", "Зигзаг без отрыва", "Закрашивает, не отрывая кисть от холста")
        self._slider(sec, "human", "Живость движений", 0, 100, 1, suffix=" %",
                     hint="Разгон, торможение, дуги и паузы. Линии остаются ровными")
        sec = Section(self, body, "Контур")
        self._slider(sec, "edge_thr", "Чувствительность", 10, 150, 1, hint="Меньше = больше линий")
        self._slider(sec, "edge_min", "Минимальная длина линии", 2, 60, 1)
        self._slider(sec, "smooth", "Сглаживание", 0, 3, 1)

    def _page_speed(self, body):
        self._header(body, "Скорость", "Чем выше скорость, тем сильнее нагрузка на процессор. Пробелов и рваных "
                                   "линий не будет: программа подстраивается под частоту вашего монитора.")
        sec = Section(self, body, "Скорость рисования")
        self._slider(sec, "speed", "Скорость", 1, 10, 1, caption=lambda v: f"{int(v)}  ·  {SPEED_NAMES[int(v)]}",
                     on_change=self._on_speed)
        self.speed_info = ctk.CTkLabel(sec.extra(), text="", font=self.f_s, text_color=C_MUTED, justify="left",
                                       anchor="w", wraplength=560)
        self.speed_info.pack(anchor="w")
        sec = Section(self, body, "Ваш компьютер")
        self.pc_labels = {}
        for key, title in (("hz", "Частота монитора"), ("timer", "Точность таймера"),
                           ("cores", "Ядра процессора"), ("rec", "Рекомендуемая скорость")):
            _row, right = sec.row(title)
            lbl = ctk.CTkLabel(right, text="…", font=self.f_b, text_color=C_MUTED)
            lbl.pack()
            self.pc_labels[key] = lbl
        block = sec.block()
        self.btn(block, "Применить рекомендуемую", self._apply_recommended, kind="primary", height=34,
                 font=self.f_b).pack(side="left")
        self.btn(block, "Проверить снова", self.run_pc_test, height=34).pack(side="left", padx=8)
        sec = Section(self, body, "Паузы игры", "Если игра не успевает переключить цвет или инструмент, увеличьте паузы.")
        self._slider(sec, "color_pause", "После нажатия кнопки", 50, 800, 10, suffix=" мс")
        self._slider(sec, "picker_pause", "На открытие палитры", 100, 1500, 10, suffix=" мс")
        self._slider(sec, "fill_pause", "После клика заливкой", 30, 600, 10, suffix=" мс")
        sec = Section(self, body, "Безопасность")
        self._switch(sec, "hide", "Прятать окно", "Во время рисования программа не заслоняет игру")
        self._switch(sec, "stop_on_move", "Стоп при движении мыши", "Если вы сдвинете мышь, рисование остановится")
        self._slider(sec, "countdown", "Отсчёт перед стартом", 0, 10, 1, suffix=" с")
        self._on_speed(self.cfg["speed"], False)

    def _page_about(self, body):
        self._header(body, "О программе", f"AutoDraw Studio {APP_VERSION}")
        sec = Section(self, body, "Обновления")
        _row, right = sec.row("Версия", "Новые версии скачиваются и устанавливаются сами")
        self.upd_status = ctk.CTkLabel(right, text=APP_VERSION, font=self.f_b, text_color=C_MUTED)
        self.upd_status.pack(side="left", padx=(0, 10))
        self.btn(right, "Проверить", lambda: self.check_updates(manual=True), width=104, height=30).pack(side="left")
        self._switch(sec, "auto_update", "Проверять при запуске")
        if not self.updater.repo:
            ctk.CTkLabel(sec.extra(), text="Источник обновлений ещё не настроен автором программы.",
                         font=self.f_s, text_color=C_FAINT).pack(anchor="w")
        sec = Section(self, body, "Горячие клавиши")
        for key, text in (("F8", "Начать рисование"), ("F9", "Пауза и продолжение"), ("Esc", "Остановить сразу"),
                          ("Ctrl+V", "Вставить картинку")):
            _row, right = sec.row(text)
            ctk.CTkLabel(right, text=key, font=self.f_s, text_color=C_TEXT, fg_color=C_SURFACE2,
                         corner_radius=6, width=56, height=26).pack()
        sec = Section(self, body, "Советы")
        ctk.CTkLabel(sec.block(), font=self.f_s, text_color=C_MUTED, justify="left", anchor="w", wraplength=560,
                     text="•  Перед стартом очистите холст в игре.\n"
                          "•  Толщина тонкой кисти во вкладке «Стиль» должна совпадать с игрой.\n"
                          "•  Если игра тормозит, уменьшите скорость на 1-2 деления.\n"
                          "•  Во время рисования не трогайте мышь, Esc останавливает в любой момент.").pack(anchor="w")


    # ------------------------------------------------------------ палитра
    def _build_palette(self):
        for w in self.pal_box.winfo_children():
            w.destroy()
        for i, c in enumerate(self.cfg["palette"]):
            if i:
                ctk.CTkFrame(self.pal_box, height=1, fg_color=C_BORDER).pack(fill="x")
            row = ctk.CTkFrame(self.pal_box, fg_color="transparent")
            row.pack(fill="x", pady=8)
            hx = rgb_hex(c["rgb"])
            ctk.CTkButton(row, text="", width=32, height=32, corner_radius=9, fg_color=hx, hover_color=hx,
                          border_width=1, border_color=C_BORDER,
                          command=lambda i=i: self._edit_color(i)).pack(side="left")
            info = ctk.CTkFrame(row, fg_color="transparent")
            info.pack(side="left", fill="x", expand=True, padx=12)
            ctk.CTkLabel(info, text=c["name"], font=self.f_b, text_color=C_TEXT if c["on"] else C_FAINT).pack(anchor="w")
            pos = f"кнопка {fmt_pos(c['pos'])}" if c["pos"] else "кнопка не указана"
            ctk.CTkLabel(info, text=f"{hx.upper()}  ·  {pos}", font=self.f_s, text_color=C_FAINT).pack(anchor="w")
            var = tk.BooleanVar(value=c["on"])
            ctk.CTkSwitch(row, text="", width=44, switch_width=40, switch_height=22, variable=var,
                          progress_color=C_ACCENT, fg_color=C_SURFACE2, button_color="#ffffff",
                          button_hover_color="#ffffff",
                          command=lambda i=i, v=var: self._toggle_color(i, v)).pack(side="right")
            if c.get("custom"):
                self.btn(row, "✕", lambda i=i: self._delete_color(i), width=30, height=30).pack(side="right", padx=6)
            self.btn(row, "◎", lambda i=i: self._pick_color(i), width=30, height=30).pack(side="right", padx=6)

    def _palette_changed(self):
        self._build_palette()
        self.save()
        self.schedule_preview()

    def _open_dialog(self, color, on_save):
        if self.dialog is not None and self.dialog.winfo_exists():
            self.dialog.lift()
            return
        self.dialog = ColorDialog(self, color, on_save)

    def _edit_color(self, i):
        c = self.cfg["palette"][i]

        def saved(res):
            c.update(res)
            self._palette_changed()
        self._open_dialog(c, saved)

    def _add_color(self):
        n = sum(1 for c in self.cfg["palette"] if c.get("custom")) + 1

        def saved(res):
            self.cfg["palette"].append({**res, "pos": None, "on": True, "custom": True})
            self._palette_changed()
        self._open_dialog({"name": f"Свой цвет {n}", "rgb": [128, 128, 128]}, saved)

    def _toggle_color(self, i, var):
        self.cfg["palette"][i]["on"] = bool(var.get())
        self._palette_changed()

    def _delete_color(self, i):
        del self.cfg["palette"][i]
        self._palette_changed()

    def _pick_color(self, i):
        c = self.cfg["palette"][i]

        def done(res):
            if res:
                c["pos"] = [int(res[0]), int(res[1])]
                self._palette_changed()
                self.toast(f"Кнопка «{c['name']}» сохранена", "ok")
        self.open_overlay("point", f"Кликните по кнопке цвета «{c['name']}»", done)

    def _on_source(self, value):
        self.src_hint.configure(text=SOURCE_HINTS.get(value, ""))

    # ------------------------------------------------------------ скорость и ПК
    def _on_speed(self, value, user: bool):
        if user:
            self.cfg["speed_auto"] = False
        timing = Timing(self.cfg, self.pc["hz"] if self.pc else None)
        text = (f"≈ {int(timing.speed_px):,} px/с по прямой  ·  углы по {timing.hold * 1000:.0f} мс  ·  "
                f"монитор {timing.hz:.0f} Гц").replace(",", " ")
        color = C_MUTED
        if timing.priority:
            text += "\nВысокий приоритет процесса во время рисования: быстрее, но сильнее нагружает ПК."
        if self.pc and value > self.pc["recommended"]:
            text += f"\nВыше рекомендуемой для этого ПК ({self.pc['recommended']}): если игра подтормаживает, возможны пропуски."
            color = C_WARN
        self.speed_info.configure(text=text, text_color=color)

    def run_pc_test(self):
        for lbl in self.pc_labels.values():
            lbl.configure(text="…", text_color=C_FAINT)
        threading.Thread(target=lambda: self.q.put(("pc", measure_pc())), daemon=True).start()

    def _on_pc(self, res: dict):
        self.pc = res
        good = res["timer_ms"] <= 0.3
        self.pc_labels["hz"].configure(text=f"{res['hz']:.0f} Гц", text_color=C_TEXT)
        self.pc_labels["timer"].configure(text=f"{res['timer_ms']:.2f} мс", text_color=C_OK if good else C_WARN)
        self.pc_labels["cores"].configure(text=str(res["cores"]), text_color=C_TEXT)
        self.pc_labels["rec"].configure(text=f"{res['recommended']}  ·  {SPEED_NAMES[res['recommended']]}",
                                        text_color=C_ACCENT_H)
        if self.cfg["speed_auto"] and self.cfg["speed"] != res["recommended"]:
            self._setters["speed"](res["recommended"])
        self._on_speed(self.cfg["speed"], False)

    def _apply_recommended(self):
        if not self.pc:
            self.run_pc_test()
            return
        self._setters["speed"](self.pc["recommended"])
        self.cfg["speed_auto"] = True
        self.save()
        self.toast(f"Скорость {self.pc['recommended']} подобрана под ваш ПК", "ok")

    # ------------------------------------------------------------ обновления
    def check_updates(self, manual: bool = False):
        if not self.updater.repo:
            if manual:
                self.toast("Источник обновлений не настроен", "warn")
            return
        if manual:
            self.upd_status.configure(text="проверяю…", text_color=C_FAINT)

        def work():
            try:
                self.q.put(("upd_found", self.updater.check(), manual))
            except Exception as e:
                self.q.put(("upd_failed", str(e), manual))
        threading.Thread(target=work, daemon=True).start()

    def _on_update_found(self, info, manual: bool):
        if info is None:
            self.upd_status.configure(text=f"{APP_VERSION}  ·  последняя", text_color=C_OK)
            if manual:
                self.toast("У вас последняя версия", "ok")
            return
        self.update_info = info
        self.upd_status.configure(text=f"доступна {info['version']}", text_color=C_ACCENT_H)
        if not self.upd_badge.winfo_ismapped():
            self.upd_badge.pack(fill="x", before=self._badge_anchor)
        if manual or info["version"] != self.cfg.get("skip_version"):
            self.after(400 if manual else 900, self._open_update)

    def _open_update(self):
        if self.update_info is None or self.busy:
            return
        if self.upd_dialog is not None and self.upd_dialog.winfo_exists():
            self.upd_dialog.lift()
            return
        self.upd_dialog = UpdateDialog(self, self.update_info)

    def download_update(self, info: dict):
        dialog = self.upd_dialog

        def work():
            try:
                path = self.updater.download(
                    info, lambda done, total: self.q.put(("upd_progress", done, total)),
                    lambda: dialog is None or dialog.cancelled)
                self.q.put(("upd_ready", path))
            except UpdateCancelled:
                pass
            except Exception as e:
                self.q.put(("upd_error", f"Не удалось скачать: {e}"))
        threading.Thread(target=work, daemon=True).start()

    def _install_update(self, path: str):
        if self.upd_dialog is not None and self.upd_dialog.winfo_exists():
            self.upd_dialog.on_ready()
        self.cfg["last_version"] = APP_VERSION
        self.save()

        def go():
            try:
                self.updater.install_and_restart(path)
            except Exception as e:
                if self.upd_dialog is not None and self.upd_dialog.winfo_exists():
                    self.upd_dialog.on_error(f"Не удалось установить: {e}")
                return
            self._quit_now()
        self.after(600, go)

    def _startup_tasks(self):
        self.updater.cleanup()
        last = self.cfg.get("last_version")
        if last and last != APP_VERSION:
            self.toast(f"Программа обновлена до версии {APP_VERSION}", "ok")
        self.cfg["last_version"] = APP_VERSION
        self.save()
        self.run_pc_test()
        if self.cfg["auto_update"]:
            self.check_updates()

    # ------------------------------------------------------------ калибровка
    def open_overlay(self, kind, text, callback) -> bool:
        if self.busy or self.overlay is not None:
            return False
        self.overlay = "pending"
        self.withdraw()

        def finish(res):
            self.overlay = None
            self.deiconify()
            self._apply_topmost()
            callback(res)

        def show():
            self.overlay = Overlay(self, kind, text, finish)

        self.after(180, show)
        return True

    def _pick_point(self, key, title, kind):
        text = "Выделите мышкой холст игры" if kind == "rect" else f"Кликните: {title.lower()}"

        def done(res):
            if res:
                self.cfg[key] = [int(v) for v in res]
                self._refresh_pos(key)
                self.save()
                self.schedule_preview()
        self.open_overlay(kind, text, done)

    def _clear_point(self, key):
        self.cfg[key] = None
        self._refresh_pos(key)
        self.save()
        self.schedule_preview()

    def test_points(self):
        if self.busy:
            return
        pts = []
        if self.cfg["canvas"]:
            x1, y1, x2, y2 = self.cfg["canvas"]
            pts += [("холст", (x1, y1)), ("холст", (x2, y1)), ("холст", (x2, y2)), ("холст", (x1, y2))]
        pts += [(name, self.cfg[key]) for key, name in CALIB_NAMES.items() if key != "canvas" and self.cfg[key]]
        pts += [(f"цвет «{c['name']}»", c["pos"]) for c in self.cfg["palette"] if c["pos"]]
        if not pts:
            self.toast("Точки ещё не заданы", "warn")
            return
        self.flags.reset()

        def run():
            mouse = Mouse()
            for name, (x, y) in pts:
                if self.flags.stop:
                    break
                self.q.put(("status", f"Проверка: {name}"))
                mouse.move(x, y)
                time.sleep(0.55)
            self.q.put(("status", "Проверка завершена"))
        threading.Thread(target=run, daemon=True).start()

    def test_rgb(self):
        if self.busy or self.overlay is not None:
            return
        missing = [CALIB_NAMES[k] for k in ("picker_btn", "field_r", "field_g", "field_b") if not self.cfg[k]]
        if missing:
            self.toast("Сначала укажите: " + ", ".join(missing), "warn")
            return
        cfg = copy.deepcopy(self.cfg)
        self._begin("Тест палитры…", hide=True)

        def run():
            try:
                time.sleep(0.4)
                Painter(cfg, self.flags, self._report).set_rgb([255, 0, 0])
                result = "Тест завершён: в игре должен выбраться красный"
            except Exception as e:
                result = f"Ошибка теста: {e}"
            self.q.put(("done", result))
        threading.Thread(target=run, daemon=True).start()

    # ------------------------------------------------------------ картинка и превью
    def open_file(self):
        path = filedialog.askopenfilename(parent=self, title="Выберите картинку", filetypes=[
            ("Изображения", "*.png *.jpg *.jpeg *.bmp *.gif *.webp"), ("Все файлы", "*.*")])
        if not path:
            return
        try:
            img = Image.open(path)
            img.load()
        except Exception as e:
            self.toast(f"Не удалось открыть файл: {e}", "bad")
            return
        self._set_image(img, os.path.basename(path))

    def paste(self):
        try:
            data = ImageGrab.grabclipboard()
        except Exception:
            data = None
        if isinstance(data, list) and data:
            try:
                data = Image.open(data[0])
                data.load()
            except Exception:
                data = None
        if isinstance(data, Image.Image):
            self._set_image(data, "из буфера обмена")
        else:
            self.toast("В буфере обмена нет картинки", "warn")

    def _set_image(self, img, name):
        self.image = img.copy()
        self.previews["Оригинал"] = prepare_image(img, {"brightness": 1, "contrast": 1, "saturation": 1})
        self.previews["Результат"] = None
        self.img_info.configure(text=f"{name}  ·  {img.width}×{img.height} px", text_color=C_OK)
        self._show_preview()
        self._update_ready()
        self._run_preview()

    def schedule_preview(self, *_):
        self._update_ready()
        if self._preview_job is not None:
            self.after_cancel(self._preview_job)
        self._preview_job = self.after(450, self._run_preview)

    def _run_preview(self):
        self._preview_job = None
        if self.image is None or self.busy:
            return
        self._plan_token += 1
        token, cfg, img = self._plan_token, copy.deepcopy(self.cfg), self.image
        rect = cfg["canvas"] or [0, 0, 800, 600]
        self._set_status("Считаю превью…")

        def work():
            try:
                self.q.put(("plan", token, Planner(cfg).build(img, rect), None))
            except Exception as e:
                self.q.put(("plan", token, None, str(e)))
        threading.Thread(target=work, daemon=True).start()

    def _on_plan(self, token, result, error):
        if token != self._plan_token:
            return                          # устаревший расчёт
        if error:
            self._set_status(f"Ошибка: {error}", C_BAD)
            return
        passes, image, stats = result
        stages = {}
        for p in passes:
            name = p.title.split(" «")[0]
            count, tool = stages.get(name, (0, p.tool))
            stages[name] = (count + len(p.strokes), tool)
        rows = [f"{i}   {name}  ·  {n} {'клик.' if tool == 'fill' else 'линий'}"
                for i, (name, (n, tool)) in enumerate(stages.items(), 1)]
        self.plan_label.configure(text="\n".join(rows) if rows else "нечего рисовать", text_color=C_MUTED)
        self.previews["Результат"] = image
        for key in ("strokes", "clicks", "seconds"):
            self._count_to(key, stats[key])
        self._show_preview()
        if self.cfg["canvas"]:
            self._set_status("Готов к рисованию  ·  F8", C_OK)
        else:
            self._set_status("Превью для холста 800×600: укажите холст в «Калибровке»", C_WARN)

    def _count_to(self, key, target):
        lbl, start = self.stat_labels[key], self._stats[key]
        self._stats[key] = float(target)

        def show(v):
            if key == "seconds":
                m, s = divmod(int(round(v)), 60)
                lbl.configure(text=f"{m}:{s:02d}")
            else:
                lbl.configure(text=f"{int(round(v)):,}".replace(",", " "))
        self.anim.tween(f"stat{key}", start, float(target), 520, show)

    def _show_preview(self):
        img = self.previews.get(self.vars["pv"].get()) or self.previews["Оригинал"]
        if img is None:
            return
        w, h = self.PREVIEW_SIZE
        k = min(w / img.width, h / img.height)
        size = (max(1, int(img.width * k)), max(1, int(img.height * k)))
        new = img.convert("RGB").resize(size, LANCZOS)
        old = self._pv_shown
        self._pv_shown = new

        def put(frame):
            self._ctk_img = ctk.CTkImage(light_image=frame, dark_image=frame, size=frame.size)
            self.pv_label.configure(image=self._ctk_img, text="")

        if old is not None and old.size == new.size:      # мягкий переход между кадрами
            self.anim.tween("preview", 0.0, 1.0, 240, lambda a: put(Image.blend(old, new, a)),
                            ease=ease_in_out, done=lambda: put(new))
        else:
            put(new)

    # ------------------------------------------------------------ рисование
    def _problems(self) -> list:
        cfg, problems = self.cfg, []
        if not cfg["canvas"]:
            problems.append("холст")
        if cfg["color_src"] == SRC_BTN:
            enabled = [c for c in cfg["palette"] if c["on"]]
            if not enabled:
                problems.append("хотя бы один цвет")
            missing = [c["name"].lower() for c in enabled if not c["pos"]]
            if missing:
                problems.append("кнопки цветов: " + ", ".join(missing))
        else:
            problems += [CALIB_NAMES[k] for k in ("picker_btn", "field_r", "field_g", "field_b") if not cfg[k]]
        if cfg["use_bucket"] and cfg["mode"] != MODES[2]:
            problems += [CALIB_NAMES[k] for k in ("brush_tool", "fill_tool") if not cfg[k]]
        return problems

    def _update_ready(self):
        if not hasattr(self, "ready_label"):
            return
        need = ([] if self.image is not None else ["картинка"]) + self._problems()
        if need:
            self.ready_label.configure(text="Осталось указать:  " + ", ".join(need), text_color=C_WARN)
        else:
            self.ready_label.configure(text="✓  Всё готово", text_color=C_OK)

    def start(self):
        if self.busy or self.overlay is not None:
            return
        if self.image is None:
            self.toast("Сначала откройте или вставьте картинку", "warn")
            return
        problems = self._problems()
        if problems:
            self.toast("Чтобы начать, укажите: " + ", ".join(problems), "warn")
            self.show_page("Калибровка")
            return
        cfg, img = copy.deepcopy(self.cfg), self.image
        self._begin("Готовлю план рисования…", hide=cfg["hide"])

        def run():
            try:
                passes, _img, _stats = Planner(cfg).build(img, cfg["canvas"])
                if passes:
                    result = Painter(cfg, self.flags, self._report).run(passes, cfg["countdown"])
                else:
                    result = "Нечего рисовать: картинка получилась пустой"
            except Exception as e:
                result = f"Ошибка: {e}"
            self.q.put(("done", result))
        threading.Thread(target=run, daemon=True).start()

    def _begin(self, text, hide):
        self.busy = True
        self.flags.reset()
        self._set_progress(0.0, animate=False)
        self.btn_draw.configure(text="Рисую…")
        self._set_status(text)
        self._pulse()
        if hide:
            self.withdraw()

    def _finish(self, text):
        self.busy = False
        self.flags.paused = False
        self.deiconify()
        self._apply_topmost()
        self.btn_draw.configure(text="Нарисовать")
        ok = text.startswith(("Готово", "Тест завершён"))
        self._set_status(text, C_OK if ok else C_WARN)
        self.toast(text, "ok" if ok else "warn")

    def _pulse(self, up: bool = True):
        """Мягко пульсирующая точка, пока идёт работа."""
        if not self.busy:
            self.dot.configure(text_color=C_FAINT)
            return
        a, b = (C_ACCENT_D, C_ACCENT_H) if up else (C_ACCENT_H, C_ACCENT_D)
        self.anim.tween("pulse", 0.0, 1.0, 650, lambda k: self.dot.configure(text_color=lerp_color(a, b, k)),
                        ease=ease_in_out, done=lambda: self._pulse(not up))

    def _set_progress(self, value: float, animate: bool = True):
        start, self._progress = self._progress, max(0.0, min(1.0, value))
        if animate:
            self.anim.tween("progress", start, self._progress, 260, self.progress.set)
        else:
            self.progress.set(self._progress)
        if self.busy:
            self.btn_draw.configure(text=f"Рисую…  {int(self._progress * 100)} %")

    def toggle_pause(self):
        if self.busy:
            self.flags.paused = not self.flags.paused
            self._set_status("Пауза" if self.flags.paused else "Продолжаю…")

    def stop(self):
        self.flags.stop = True
        if not self.busy:
            self._set_status("Остановлено")

    # ------------------------------------------------------------ служебное
    def _report(self, *msg):
        """Вызывается из фоновых потоков: только кладёт сообщение в очередь."""
        self.q.put(msg)

    def _poll(self):
        try:
            while True:
                msg = self.q.get_nowait()
                kind = msg[0]
                if kind == "status":
                    self._set_status(msg[1])
                elif kind == "progress":
                    self._set_progress(msg[1])
                elif kind == "done":
                    self._finish(msg[1])
                elif kind == "plan":
                    self._on_plan(*msg[1:])
                elif kind == "pc":
                    self._on_pc(msg[1])
                elif kind == "upd_found":
                    self._on_update_found(msg[1], msg[2])
                elif kind == "upd_failed":
                    self.upd_status.configure(text=APP_VERSION, text_color=C_MUTED)
                    if msg[2]:
                        self.toast("Не удалось проверить обновления. Проверьте интернет.", "warn")
                elif kind in ("upd_progress", "upd_error") and self.upd_dialog is not None \
                        and self.upd_dialog.winfo_exists():
                    if kind == "upd_progress":
                        self.upd_dialog.on_progress(msg[1], msg[2])
                    else:
                        self.upd_dialog.on_error(msg[1])
                elif kind == "upd_ready":
                    self._install_update(msg[1])
                elif kind == "hotkey":
                    if msg[1] == "esc" and isinstance(self.overlay, Overlay):
                        self.overlay.finish(None)
                    elif msg[1] == "start":
                        self.start()
        except queue.Empty:
            pass
        self.after(30, self._poll)

    def _on_hotkey(self, key):
        """Поток pynput: флаги меняем сразу, интерфейс только через очередь."""
        if key == keyboard.Key.esc:
            self.flags.stop = True
            self.q.put(("hotkey", "esc"))
        elif key == keyboard.Key.f9:
            if self.busy:
                self.flags.paused = not self.flags.paused
        elif key == keyboard.Key.f8:
            self.q.put(("hotkey", "start"))

    def _on_ctrl(self, e):
        if isinstance(e.widget, tk.Entry) or isinstance(e.widget, tk.Text):
            return
        if e.keysym.lower() in ("v", "м", "cyrillic_em") or e.keycode == 86:
            self.paste()

    def _set_status(self, text, color=C_MUTED):
        self.status.configure(text=text, text_color=color)

    def _apply_topmost(self):
        self.cfg["topmost"] = bool(self.vars["topmost"].get())
        self.attributes("-topmost", self.cfg["topmost"])

    def save(self):
        save_settings(self.cfg)

    def _quit_now(self):
        self.flags.stop = True
        try:
            self.listener.stop()
        except Exception:
            pass
        try:
            self.destroy()
        finally:
            os._exit(0)

    def _on_close(self):
        self.flags.stop = True
        self.save()
        self.anim.tween("window", 1.0, 0.0, 160, lambda a: self.attributes("-alpha", a), done=self._quit_now)


def main():
    ctk.set_appearance_mode("dark")
    ctk.set_default_color_theme("blue")
    App().mainloop()


if __name__ == "__main__":
    main()
