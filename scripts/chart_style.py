"""Shared visual language for SVG charts on the Tau Ceti statistics page."""

BG = "#101936"
PANEL = "#1b2547"
BAR_BG = "#27335a"
GRID = "rgba(255,255,255,0.08)"
AXIS = "rgba(255,255,255,0.18)"
TEXT = "#eef2fb"
MUTED = "#9aa6c9"
FONT_FAMILY = "ui-sans-serif,system-ui,-apple-system,'Segoe UI',Roboto,sans-serif"

# Distinct on the navy background; tools may assign these by order or stable hash.
PALETTE = [
    "#5eead4", "#ff9d4d", "#60a5fa", "#fb7185", "#c084fc", "#4ade80",
    "#fde047", "#22d3ee", "#f472b6", "#a3e635", "#818cf8", "#fb923c",
    "#38bdf8", "#f87171", "#2dd4bf", "#e879f9",
]

BASE_CSS = (
    f"text{{font-family:{FONT_FAMILY};fill:{TEXT}}}"
    ".title{font-size:19px;font-weight:600}"
    f".subtitle{{font-size:13px;fill:{MUTED}}}"
)


def card_rect(width: int, height: int) -> str:
    """The common rounded chart background and border."""
    return (
        f'<rect x="0.5" y="0.5" width="{width-1}" height="{height-1}" '
        f'rx="12" fill="{BG}" stroke="{PANEL}"/>'
    )
