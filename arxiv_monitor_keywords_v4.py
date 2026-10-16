import argparse
import copy
import html
import json
import os
import re
import smtplib
import time
import unicodedata
from dataclasses import dataclass
from datetime import datetime, timedelta
from email.message import EmailMessage
from pathlib import Path
from typing import Iterable
from urllib.parse import urljoin
from zoneinfo import ZoneInfo

import requests
from bs4 import BeautifulSoup


# ==== 用户设置 ====
BASE_URL = "https://arxiv.org"
URL = f"{BASE_URL}/list/cond-mat/new?skip=0&show=2000"
PASTWEEK_URL = f"{BASE_URL}/list/cond-mat/pastweek?skip=0&show=2000"
CHECK_INTERVAL = 120
# GitHub-hosted job 最长通常设置为 360 分钟。这里最多轮询 5 小时 40 分钟，
# 给 PDF、邮件及最后提交状态文件预留约 20 分钟。
RUN_LIMIT = 5 * 60 * 60 + 40 * 60
STATE_RETENTION_DAYS = 60
DEFAULT_STATE_PATH = (
    Path(__file__).resolve().parent / "state" / "arxiv_monitor_state.json"
)

EMAIL_FROM = os.environ.get("EMAIL_FROM")  # 你的 QQ 邮箱账号，用来登录 SMTP
EMAIL_PASS = os.environ.get("EMAIL_PASS")
EMAIL_TO = os.environ.get("EMAIL_TO")
EMAIL_TO_2 = os.environ.get("EMAIL_TO_2") or os.environ.get("EMAIL_TO_CRK")
SMTP_SERVER = "smtp.qq.com"
SMTP_PORT = 465

# 仅以下关键词命中时自动下载 PDF；其他 KEYWORDS 只发送提醒。
IMPORTANT_KEYWORDS = [
    "Andrea F. Young",
    "Brian D.Gerardot",
    "Chun Hung Lui",
    "Feng Wang",
    "Imamoglu",
    "Jiaqi Cai",
    "Jie Shan",
    "Kin Fai Mak",
    "Libai Huang",
    "MacDonald",
    "Sufei Shi",
    "Yanhao Tang",
    "TingXin Li",
    "Tony F. Heinz",
    "Xiaodong Xu",
    "Xiaoyang Zhu",
    "YongTao Cui",
    "Ziliang Ye",
]
DOWNLOAD_DIR = Path(__file__).resolve().parent / "downloads"
# 邮件采用 Base64 编码后体积会增大；这里限制原始 PDF 附件总量。
MAX_EMAIL_ATTACHMENT_BYTES = 12 * 1024 * 1024
MAX_PDF_BYTES = 50 * 1024 * 1024

# 之后想到新的关键词，直接追加到这个列表里即可。列表按首字母排序，方便查找。
KEYWORDS = [
    "Allan H. MacDonald",
    "Andrea F. Young",
    "Anlian Pan",
    "Brian D. Gerardot",
    "Brian D.Gerardot",
    "Chenhao Jin",
    "Chih-Kang Shih",
    "Chun Hung Lui",
    "Di Xiao",
    "Eric Anderson",
    "Erfu Liu",
    "Eslam Khalaf",
    "Feng Wang",
    "Fengcheng Wu",
    "Heonjoon Park",
    "Hongyi Yu",
    "Imamoglu",
    "Jiaqi Cai",
    "Jie Shan",
    "jie gu",
    "Jun Yan",
    "Kaifei Kang",
    "kenji",
    "Kenji Watanabe",
    "Kin Fai Mak",
    "Liang Fu",
    "Libai Huang",
    "Long Ju",
    "MacDonald",
    "moire",
    "MoS2",
    "MoSe2",
    "MoTe2",
    "Pablo Jarillo-Herrero",
    "Sufei Shi",
    "Takashi Taniguchi",
    "Yanhao Tang",
    "Ting Cao",
    "TingXin Li",
    "TMD",
    "Tony F. Heinz",
    "Weibo Gao",
    "WS2",
    "WSe2",
    "Xiaodong Xu",
    "Xiaoqin Li",
    "Xiaoxue Liu",
    "Xiaoyang Zhu",
    "Yao Wang",
    "Yimo Han",
    "YongTao Cui",
    "Yuanbo Zhang",
    "Ziliang Ye",
]


SUBSCRIPT_TRANSLATION = str.maketrans(
    {
        "₀": "0",
        "₁": "1",
        "₂": "2",
        "₃": "3",
        "₄": "4",
        "₅": "5",
        "₆": "6",
        "₇": "7",
        "₈": "8",
        "₉": "9",
        "⁰": "0",
        "¹": "1",
        "²": "2",
        "³": "3",
        "⁴": "4",
        "⁵": "5",
        "⁶": "6",
        "⁷": "7",
        "⁸": "8",
        "⁹": "9",
    }
)

SECTION_NAMES = {
    "new submissions": "New submissions",
    "cross submissions": "Cross submissions",
    "replacement submissions": "Replacement submissions",
}


@dataclass
class ArxivPaper:
    index: str
    arxiv_id: str
    title: str
    authors: str
    abstract_text: str
    abs_url: str
    pdf_url: str
    matched_keywords: list[str]
    download_path: Path | None = None
    download_error: str | None = None
    attached_to_email: bool = False
    attachment_note: str | None = None


@dataclass
class ArxivSection:
    name: str
    heading: str
    total_entries: int
    shown_entries: int
    papers: list[ArxivPaper]


def fetch_soup(url: str = URL) -> BeautifulSoup:
    response = requests.get(
        url,
        timeout=30,
        headers={"User-Agent": "arxiv-cond-mat-monitor/4.0"},
    )
    response.raise_for_status()
    return BeautifulSoup(response.text, "html.parser")


def parse_header_date(header_text: str):
    date_str = header_text.replace("Showing new listings for ", "")
    return datetime.strptime(date_str, "%A, %d %B %Y").date()


def get_listing_header(soup: BeautifulSoup):
    for header in soup.find_all("h3"):
        text = header.get_text(" ", strip=True)
        if text.startswith("Showing new listings for "):
            return text
    return None


def get_today_update_status(soup: BeautifulSoup):
    header_text = get_listing_header(soup)
    if not header_text:
        return False, None

    try:
        header_date = parse_header_date(header_text)
        today = datetime.now(ZoneInfo("Asia/Shanghai")).date()
        return header_date == today, header_text
    except Exception as exc:
        print("日期解析失败:", exc)
        return False, header_text


def empty_state() -> dict:
    return {
        "version": 1,
        "updated_at": None,
        "processed_ids": {},
        "reported_listing_dates": [],
    }


def load_state(path: Path) -> tuple[dict, bool]:
    """Load durable monitor state.

    A malformed existing state is treated as a hard error.  Silently replacing
    it would make every recent paper look new and could send duplicate mail.
    """
    if not path.exists():
        return empty_state(), False
    with path.open("r", encoding="utf-8") as handle:
        state = json.load(handle)
    if not isinstance(state, dict) or not isinstance(state.get("processed_ids"), dict):
        raise ValueError(f"状态文件格式无效：{path}")
    state.setdefault("version", 1)
    state.setdefault("updated_at", None)
    state.setdefault("reported_listing_dates", [])
    return state, True


def prune_state(state: dict, now: datetime) -> None:
    cutoff = (now.date() - timedelta(days=STATE_RETENTION_DAYS)).isoformat()
    state["processed_ids"] = {
        arxiv_id: processed_date
        for arxiv_id, processed_date in state.get("processed_ids", {}).items()
        if isinstance(processed_date, str) and processed_date >= cutoff
    }
    state["reported_listing_dates"] = sorted(
        {
            value
            for value in state.get("reported_listing_dates", [])
            if isinstance(value, str) and value >= cutoff
        }
    )


def save_state(path: Path, state: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    with temporary.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(state, handle, ensure_ascii=False, indent=2, sort_keys=True)
        handle.write("\n")
    temporary.replace(path)


def clean_label_text(text: str, label: str) -> str:
    text = " ".join(text.split())
    if text.lower().startswith(label.lower()):
        return text[len(label) :].strip()
    return text


def unique_keep_order(items: Iterable[str]) -> list[str]:
    seen = set()
    result = []
    for item in items:
        normalized = item.strip()
        if not normalized:
            continue
        key = normalized.casefold()
        if key in seen:
            continue
        seen.add(key)
        result.append(normalized)
    return result


def normalize_for_search(text: str) -> str:
    text = text.translate(SUBSCRIPT_TRANSLATION)
    text = unicodedata.normalize("NFKD", text.casefold())
    return "".join(char for char in text if not unicodedata.combining(char))


def compact_formula_text(text: str) -> str:
    text = normalize_for_search(text)
    text = re.sub(r"\\[a-zA-Z]+", "", text)
    text = re.sub(r"[\s_\$\{\}\^\(\)\[\],.;:~`'\"+-]+", "", text)
    return text


def tokenize_for_exact_search(text: str) -> str:
    """Normalize text into space-delimited alphanumeric tokens.

    Padding with spaces lets callers perform an exact token/phrase lookup.  In
    particular, a keyword such as ``Yao Wang`` must not match the tail of
    ``Xiyao Wang``.
    """
    normalized = normalize_for_search(text)
    tokens = re.findall(r"[a-z0-9]+", normalized)
    return " " + " ".join(tokens) + " "


def find_keywords(search_text: str) -> list[str]:
    tokenized_text = tokenize_for_exact_search(search_text)
    compact_text = compact_formula_text(search_text)

    matched = []
    for keyword in KEYWORDS:
        tokenized_keyword = tokenize_for_exact_search(keyword).strip()
        compact_keyword = compact_formula_text(keyword)
        is_formula_keyword = any(char.isdigit() for char in compact_keyword)
        # Exact token boundaries prevent person-name substring false positives:
        # Yao Wang != Xiyao Wang, Jie Gu != Jie Guan, Jun Yan != Jun Yang.
        exact_phrase = f" {tokenized_keyword} " in tokenized_text
        if exact_phrase or (
            is_formula_keyword and compact_keyword in compact_text
        ):
            matched.append(keyword)

    return unique_keep_order(matched)


def parse_section_counts(heading: str) -> tuple[int | None, int | None]:
    match = re.search(r"showing\s+(\d+)\s+of\s+(\d+)\s+entries", heading, re.IGNORECASE)
    if not match:
        return None, None
    return int(match.group(1)), int(match.group(2))


def parse_section_name(heading: str) -> str | None:
    lowered = heading.casefold()
    for key, name in SECTION_NAMES.items():
        if key in lowered:
            return name
    return None


def parse_papers_from_entries(entries) -> list[ArxivPaper]:
    papers = []
    seen_arxiv_ids = set()

    for dt, dd in entries:
        index_link = dt.find("a", href=False)
        index = index_link.get_text(" ", strip=True) if index_link else ""

        abs_link = dt.find("a", href=lambda href: href and href.startswith("/abs/"))
        if not abs_link:
            continue

        arxiv_id = abs_link.get_text(" ", strip=True).replace("arXiv:", "").strip()
        if not arxiv_id or arxiv_id in seen_arxiv_ids:
            continue
        seen_arxiv_ids.add(arxiv_id)

        title_tag = dd.find(class_="list-title")
        authors_tag = dd.find(class_="list-authors")

        title = clean_label_text(
            title_tag.get_text(" ", strip=True) if title_tag else "",
            "Title:",
        )
        authors = authors_tag.get_text(" ", strip=True) if authors_tag else ""

        dd_for_abstract = copy.deepcopy(dd)
        for tag in dd_for_abstract.find_all(
            class_=["list-title", "list-authors", "list-comments", "list-journal-ref", "list-subjects"]
        ):
            tag.extract()
        abstract_text = " ".join(dd_for_abstract.stripped_strings)

        search_text = f"{title}\n{authors}\n{abstract_text}"
        matched_keywords = find_keywords(search_text)

        papers.append(
            ArxivPaper(
                index=index,
                arxiv_id=arxiv_id,
                title=title,
                authors=authors,
                abstract_text=abstract_text,
                abs_url=urljoin(URL, f"/abs/{arxiv_id}"),
                pdf_url=f"https://arxiv.org/pdf/{arxiv_id}#zoom=200",
                matched_keywords=matched_keywords,
            )
        )

    return papers


def collect_section_entries(header) -> list[tuple]:
    entries = []
    current_dt = None
    node = header.find_next_sibling()

    while node:
        if node.name == "h3" and parse_section_name(node.get_text(" ", strip=True)):
            break

        if node.name == "dt":
            current_dt = node
        elif node.name == "dd" and current_dt is not None:
            entries.append((current_dt, node))
            current_dt = None

        node = node.find_next_sibling()

    return entries


def parse_sections(soup: BeautifulSoup) -> list[ArxivSection]:
    sections = []
    seen_section_names = set()

    for header in soup.find_all("h3"):
        heading = header.get_text(" ", strip=True)
        section_name = parse_section_name(heading)
        if not section_name or section_name in seen_section_names:
            continue

        entries = collect_section_entries(header)
        papers = parse_papers_from_entries(entries)
        shown_entries, total_entries = parse_section_counts(heading)

        sections.append(
            ArxivSection(
                name=section_name,
                heading=heading,
                shown_entries=shown_entries if shown_entries is not None else len(papers),
                total_entries=total_entries if total_entries is not None else len(papers),
                papers=papers,
            )
        )
        seen_section_names.add(section_name)

    return sections


def listing_completeness(sections: list[ArxivSection]) -> tuple[bool, str]:
    """Reject the transitional page that can expose replacements first."""
    section_by_name = {section.name: section for section in sections}
    new_section = section_by_name.get("New submissions")
    if new_section is None:
        return False, "页面尚未出现 New submissions 分区"
    if not new_section.papers:
        return False, "New submissions 分区暂时为空"

    for section in sections:
        parsed = len(section.papers)
        if parsed != section.shown_entries:
            return (
                False,
                f"{section.name} 只解析到 {parsed}/{section.shown_entries} 篇",
            )
        if section.shown_entries != section.total_entries:
            return (
                False,
                f"{section.name} 页面只展示 {section.shown_entries}/{section.total_entries} 篇",
            )
    return True, "页面分区及条目数量完整"


def listing_fingerprint(header_text: str, sections: list[ArxivSection]) -> tuple:
    return (
        header_text,
        tuple(
            (
                section.name,
                section.shown_entries,
                section.total_entries,
                tuple(paper.arxiv_id for paper in section.papers),
            )
            for section in sections
        ),
    )


def parse_pastweek_papers(soup: BeautifulSoup) -> list[ArxivPaper]:
    entries = []
    for dt in soup.find_all("dt"):
        dd = dt.find_next_sibling("dd")
        if dd is not None:
            entries.append((dt, dd))
    return parse_papers_from_entries(entries)


def unique_papers(papers: Iterable[ArxivPaper]) -> list[ArxivPaper]:
    seen_ids = set()
    result = []
    for paper in papers:
        if paper.arxiv_id and paper.arxiv_id not in seen_ids:
            seen_ids.add(paper.arxiv_id)
            result.append(paper)
    return result


def filter_sections(
    sections: list[ArxivSection], allowed_ids: set[str]
) -> list[ArxivSection]:
    return [
        ArxivSection(
            name=section.name,
            heading=section.heading,
            total_entries=section.total_entries,
            shown_entries=section.shown_entries,
            papers=[paper for paper in section.papers if paper.arxiv_id in allowed_ids],
        )
        for section in sections
    ]


def is_important_paper(paper: ArxivPaper) -> bool:
    # 忽略空格差异，以便 Brian D.Gerardot 和 Brian D. Gerardot 都能命中。
    important = {re.sub(r"\s+", "", word).casefold() for word in IMPORTANT_KEYWORDS}
    return any(
        re.sub(r"\s+", "", word).casefold() in important
        for word in paper.matched_keywords
    )


def clean_pdf_title(title: str) -> str:
    """沿用 DownloadPaper3.1_gpt 中 arXiv 标题的文件名清理规则。"""
    title = html.unescape(title)
    title = re.sub(r"<[^>]*>", "", title)
    title = re.sub(r"\\(?:mathrm|ensuremath)", "", title)
    title = re.sub(r"(?:mathrm|ensuremath)", "", title)
    title = title.replace("$_", "").replace("}_", "")
    title = title.replace(r"\text{", "").replace("text{", "")
    title = title.replace("/", "-")
    title = re.sub(r"[$\{\}]", "", title)
    title = re.sub(r'[<>:"/\\|?*]', "", title)
    title = re.sub(r"[\x00-\x1f\x7f]", "", title)
    title = re.sub(r"\s+", " ", title).strip(" .")
    return title or "Untitled"


def normalize_paper_date(date_text: str) -> str:
    match = re.match(r"^(\d{4})[/-](\d{1,2})[/-](\d{1,2})", date_text.strip())
    if match:
        year, month, day = map(int, match.groups())
        return f"{year:04d}-{month:02d}-{day:02d}"
    for date_format in ("%d %B %Y", "%d %b %Y", "%B %d, %Y", "%b %d, %Y"):
        try:
            return datetime.strptime(date_text.strip(), date_format).strftime("%Y-%m-%d")
        except ValueError:
            continue
    return ""


def get_paper_filename(paper: ArxivPaper, session: requests.Session) -> str:
    with session.get(paper.abs_url, timeout=30) as response:
        response.raise_for_status()
        soup = BeautifulSoup(response.text, "html.parser")

    title_meta = soup.find("meta", attrs={"name": "citation_title"})
    title = title_meta.get("content", "").strip() if title_meta else ""
    title = clean_pdf_title(title or paper.title)

    date_text = ""
    for name in ("citation_online_date", "citation_date"):
        date_meta = soup.find("meta", attrs={"name": name})
        if date_meta and date_meta.get("content"):
            date_text = normalize_paper_date(date_meta["content"])
            if date_text:
                break
    if not date_text:
        history = soup.find(class_="submission-history")
        if history:
            match = re.search(
                r"Submitted\s+on\s+(\d{1,2}\s+[A-Za-z]+\s+\d{4})",
                history.get_text(" ", strip=True),
            )
            if match:
                date_text = normalize_paper_date(match.group(1))
    if not date_text:
        # arXiv 编号可提供保底年月；优先使用摘要页中的发布日期。
        match = re.match(r"(\d{2})(\d{2})\.", paper.arxiv_id)
        date_text = f"20{match.group(1)}-{match.group(2)}" if match else "unknown-date"

    prefix = f"{date_text} - arXiv - "
    # 默认目录在 Windows 上也可能接近旧版 260 字符路径上限。
    max_title_length = 180 - len(prefix) - len(".pdf")
    return f"{prefix}{title[:max_title_length].rstrip(' .') or 'Untitled'}.pdf"


def download_paper(paper: ArxivPaper, session: requests.Session) -> Path:
    filename = get_paper_filename(paper, session)
    DOWNLOAD_DIR.mkdir(parents=True, exist_ok=True)
    destination = DOWNLOAD_DIR / filename
    if destination.is_file() and destination.stat().st_size > 0:
        print(f"PDF 已存在，跳过下载：{destination.name}")
        return destination

    temporary = destination.with_name(destination.name + ".part")
    try:
        with session.get(paper.pdf_url.split("#", 1)[0], timeout=60, stream=True) as response:
            response.raise_for_status()
            downloaded = 0
            with temporary.open("wb") as output:
                for chunk in response.iter_content(chunk_size=128 * 1024):
                    if not chunk:
                        continue
                    if downloaded == 0 and not chunk.lstrip().startswith(b"%PDF"):
                        raise ValueError("服务器返回的内容不是 PDF")
                    downloaded += len(chunk)
                    if downloaded > MAX_PDF_BYTES:
                        raise ValueError("PDF 超过 50 MB 下载上限")
                    output.write(chunk)
                if downloaded == 0:
                    raise ValueError("服务器返回空 PDF")
        temporary.replace(destination)
    except Exception:
        temporary.unlink(missing_ok=True)
        raise
    print(f"PDF 下载完成：{destination}")
    return destination


def download_important_papers(sections: list[ArxivSection]) -> None:
    results: dict[str, tuple[Path | None, str | None]] = {}
    with requests.Session() as session:
        session.headers.update({"User-Agent": "arxiv-cond-mat-monitor/4.0"})
        for section in sections:
            for paper in section.papers:
                if not is_important_paper(paper):
                    continue
                if paper.arxiv_id not in results:
                    try:
                        results[paper.arxiv_id] = (download_paper(paper, session), None)
                    except Exception as exc:
                        results[paper.arxiv_id] = (None, str(exc))
                        print(f"PDF 下载失败（arXiv:{paper.arxiv_id}）：{exc}")
                paper.download_path, paper.download_error = results[paper.arxiv_id]


def prepare_email_attachments(
    sections: list[ArxivSection],
) -> list[tuple[str, bytes]]:
    attachments: list[tuple[str, bytes]] = []
    attached_paths: set[Path] = set()
    total_bytes = 0
    for section in sections:
        for paper in section.papers:
            path = paper.download_path
            if path is None:
                continue
            if path in attached_paths:
                paper.attached_to_email = True
                continue
            try:
                size = path.stat().st_size
                if total_bytes + size > MAX_EMAIL_ATTACHMENT_BYTES:
                    paper.attachment_note = "PDF 附件总大小超过 12 MB，未附在邮件中"
                    continue
                data = path.read_bytes()
            except OSError as exc:
                paper.attachment_note = f"读取附件失败：{exc}"
                continue
            attachments.append((path.name, data))
            attached_paths.add(path)
            total_bytes += len(data)
            paper.attached_to_email = True
    return attachments


def build_email_content(header_text: str, sections: list[ArxivSection]) -> tuple[str, str]:
    total_papers = sum(len(section.papers) for section in sections)
    matched_papers = [
        paper
        for section in sections
        for paper in section.papers
        if paper.matched_keywords
    ]

    if matched_papers:
        subject = f"ArXiv cond-mat 今日更新，关键词命中 {len(matched_papers)} 篇"
    else:
        subject = "ArXiv cond-mat 今日有更新，但暂无关键词命中"

    lines = [
        f"更新标题: {header_text}",
        f"页面链接: {URL}",
        f"本次共解析到 {total_papers} 篇文献。",
        "",
    ]

    for section in sections:
        matched = [paper for paper in section.papers if paper.matched_keywords]
        lines.extend(
            [
                f"====={section.name}=====",
                f"关键词命中：{len(matched)}/{section.total_entries}",
                "",
            ]
        )

        if not matched:
            lines.append("本部分暂无关键词命中。")
            lines.append("")
            continue

        for number, paper in enumerate(matched, start=1):
            lines.extend(
                [
                    f"{number}. {paper.index} arXiv:{paper.arxiv_id}",
                    f"标题: {paper.title}",
                    f"作者: {paper.authors}",
                    f"命中关键词: {', '.join(paper.matched_keywords)}",
                    f"PDF: {paper.pdf_url}",
                    f"摘要页: {paper.abs_url}",
                ]
            )
            if paper.download_path:
                if paper.attached_to_email:
                    lines.append(f"已下载：见邮件附件《{paper.download_path.name}》（手机和电脑均可打开）")
                else:
                    lines.append(f"已下载：{paper.download_path.name}（保存在运行脚本的设备上）")
                    if paper.attachment_note:
                        lines.append(f"附件提示：{paper.attachment_note}")
            elif paper.download_error:
                lines.append(f"自动下载失败：{paper.download_error}；仍可使用上方 PDF 链接")
            lines.append("")

    if not sections:
        lines.append("已检测到今日更新，但没有解析到 New/Cross/Replacement 分区。")

    return subject, "\n".join(lines).strip()


def get_email_recipients() -> list[str]:
    return unique_keep_order(email for email in [EMAIL_TO, EMAIL_TO_2] if email)


def send_email(
    subject: str,
    content: str,
    attachments: list[tuple[str, bytes]] | None = None,
) -> bool:
    recipients = get_email_recipients()
    if not EMAIL_FROM or not EMAIL_PASS or not recipients:
        print("邮箱账号、授权码或收件人不完整，跳过发送邮件。")
        print("邮件主题:", subject)
        print("邮件内容:\n", content)
        return False

    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = EMAIL_FROM
    msg["To"] = ", ".join(recipients)
    msg.set_content(content)
    for filename, data in attachments or []:
        msg.add_attachment(data, maintype="application", subtype="pdf", filename=filename)

    try:
        with smtplib.SMTP_SSL(SMTP_SERVER, SMTP_PORT) as server:
            server.login(EMAIL_FROM, EMAIL_PASS)
            server.send_message(msg, from_addr=EMAIL_FROM, to_addrs=recipients)
        print(f"邮件已发送：{subject}，收件人：{recipients}")
        return True
    except Exception as exc:
        print("发送邮件失败:", exc)
        return False


def check_once():
    soup = fetch_soup(URL)
    has_update, header_text = get_today_update_status(soup)
    if not has_update:
        return False, header_text, [], False, "页面尚未切换到北京时间当天"
    sections = parse_sections(soup)
    complete, reason = listing_completeness(sections)
    return True, header_text, sections, complete, reason


def build_candidate_sections(
    current_sections: list[ArxivSection],
    pastweek_papers: list[ArxivPaper],
    processed_ids: set[str],
    state_existed: bool,
) -> tuple[list[ArxivSection], set[str], set[str], int]:
    current_ids = {
        paper.arxiv_id for section in current_sections for paper in section.papers
    }
    pastweek_papers = unique_papers(pastweek_papers)
    pastweek_ids = {paper.arxiv_id for paper in pastweek_papers}
    visible_ids = current_ids | pastweek_ids

    if state_existed:
        candidate_ids = visible_ids - processed_ids
        baseline_count = 0
    else:
        # First v4 run: notify only the current complete daily listing and
        # silently baseline older papers already present in the past-week page.
        candidate_ids = set(current_ids)
        baseline_count = len(pastweek_ids - current_ids)

    report_sections = filter_sections(current_sections, candidate_ids)
    recovered = [
        paper
        for paper in pastweek_papers
        if paper.arxiv_id in candidate_ids and paper.arxiv_id not in current_ids
    ]
    if recovered:
        report_sections.append(
            ArxivSection(
                name="Recent-week recovery",
                heading="最近一周补漏",
                total_entries=len(recovered),
                shown_entries=len(recovered),
                papers=recovered,
            )
        )
    return report_sections, visible_ids, candidate_ids, baseline_count


def process_complete_listing(
    header_text: str,
    sections: list[ArxivSection],
    state_path: Path,
) -> bool:
    state, state_existed = load_state(state_path)
    now = datetime.now(ZoneInfo("Asia/Shanghai"))
    prune_state(state, now)

    pastweek_soup = fetch_soup(PASTWEEK_URL)
    pastweek_papers = parse_pastweek_papers(pastweek_soup)
    processed_ids = set(state["processed_ids"])
    report_sections, visible_ids, candidate_ids, baseline_count = build_candidate_sections(
        sections,
        pastweek_papers,
        processed_ids,
        state_existed,
    )

    listing_date = parse_header_date(header_text).isoformat()
    already_reported = listing_date in state["reported_listing_dates"]
    print(
        "状态统计："
        f"已记录={len(processed_ids)}，当前完整页={sum(len(s.papers) for s in sections)}，"
        f"最近一周={len(pastweek_papers)}，本次新增/补漏={len(candidate_ids)}"
    )
    if baseline_count:
        print(f"首次使用 v4：将 {baseline_count} 篇较早条目登记为基线，不发送旧文献。")

    if not candidate_ids and already_reported:
        print(f"{listing_date} 已成功汇报且没有新的补漏条目，本次不重复发送邮件。")
        state["updated_at"] = now.isoformat(timespec="seconds")
        save_state(state_path, state)
        return True

    download_important_papers(report_sections)
    attachments = prepare_email_attachments(report_sections)
    subject, content = build_email_content(header_text, report_sections)
    content += (
        "\n\n去重与补漏："
        f"最近一周共检查 {len(pastweek_papers)} 篇；"
        f"本次首次处理 {len(candidate_ids)} 篇。"
    )
    if not send_email(subject, content, attachments):
        print("邮件未成功发送，状态文件不更新；下次运行会再次尝试。")
        return False

    processed_date = now.date().isoformat()
    for arxiv_id in visible_ids:
        state["processed_ids"][arxiv_id] = processed_date
    state["reported_listing_dates"] = sorted(
        set(state["reported_listing_dates"]) | {listing_date}
    )
    state["updated_at"] = now.isoformat(timespec="seconds")
    prune_state(state, now)
    save_state(state_path, state)
    print(f"状态文件已更新：{state_path}（{len(state['processed_ids'])} 个 ID）")
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description="Monitor arXiv cond-mat new papers.")
    parser.add_argument(
        "--test-send",
        action="store_true",
        help="抓取当前页面并立即发送测试邮件；不检查日期，也不自动下载 PDF。",
    )
    parser.add_argument(
        "--check-now",
        action="store_true",
        help="只读检查当前页面完整性、最近一周数量和状态文件；不发邮件、不写状态。",
    )
    parser.add_argument(
        "--state-path",
        type=Path,
        default=DEFAULT_STATE_PATH,
        help=f"状态文件路径（默认：{DEFAULT_STATE_PATH}）",
    )
    args = parser.parse_args()

    if args.test_send:
        soup = fetch_soup(URL)
        _, header_text = get_today_update_status(soup)
        sections = parse_sections(soup)
        subject, content = build_email_content(header_text or "arXiv cond-mat 当前页面", sections)
        return 0 if send_email("[测试] " + subject, content) else 2

    if args.check_now:
        soup = fetch_soup(URL)
        has_update, header_text = get_today_update_status(soup)
        sections = parse_sections(soup)
        complete, reason = listing_completeness(sections)
        state, state_existed = load_state(args.state_path)
        pastweek_papers = parse_pastweek_papers(fetch_soup(PASTWEEK_URL))
        print(f"页面标题：{header_text or '未找到'}")
        print(f"是否为北京时间当天：{has_update}")
        for section in sections:
            print(
                f"- {section.name}: parsed={len(section.papers)}, "
                f"shown={section.shown_entries}, total={section.total_entries}"
            )
        print(f"页面完整性：{complete}；{reason}")
        print(f"最近一周条目：{len(pastweek_papers)}")
        print(
            f"状态文件：{'已存在' if state_existed else '尚未创建'}；"
            f"已记录 ID={len(state['processed_ids'])}"
        )
        return 0 if complete else 1

    start_time = datetime.now()
    stable_fingerprint = None
    last_status = "尚未读取页面"

    print(f"当前系统时间（UTC）: {datetime.now(ZoneInfo('UTC'))}")
    print(f"北京时间: {datetime.now(ZoneInfo('Asia/Shanghai'))}")
    print(f"[{datetime.now()}] 开始检测 arXiv cond-mat 当天更新和关键词...")

    while (datetime.now() - start_time).total_seconds() < RUN_LIMIT:
        try:
            has_update, header_text, sections, complete, reason = check_once()
        except Exception as exc:
            print(f"[{datetime.now()}] 检查失败，等待下一次重试: {exc}")
            stable_fingerprint = None
            last_status = f"检查失败：{exc}"
            time.sleep(CHECK_INTERVAL)
            continue

        if not has_update:
            stable_fingerprint = None
            last_status = reason
            print(f"[{datetime.now()}] {reason}，等待下一次检查...")
            time.sleep(CHECK_INTERVAL)
            continue

        if not complete:
            stable_fingerprint = None
            last_status = reason
            print(f"[{datetime.now()}] 页面日期已更新但内容不完整：{reason}；两分钟后重试。")
            time.sleep(CHECK_INTERVAL)
            continue

        fingerprint = listing_fingerprint(header_text, sections)
        if fingerprint != stable_fingerprint:
            stable_fingerprint = fingerprint
            last_status = "完整页面首次确认，等待下一轮稳定性复核"
            print(f"[{datetime.now()}] {reason}；等待两分钟后再次确认页面稳定。")
            time.sleep(CHECK_INTERVAL)
            continue

        try:
            success = process_complete_listing(header_text, sections, args.state_path)
        except Exception as exc:
            print(f"[{datetime.now()}] 补漏或状态处理失败，等待重试：{exc}")
            last_status = f"补漏或状态处理失败：{exc}"
            time.sleep(CHECK_INTERVAL)
            continue
        return 0 if success else 2

    timeout_content = (
        "截至运行时间上限，仍未获得稳定且完整的当天更新页面。\n"
        f"最后状态：{last_status}\n"
        "程序没有写入新的已处理 ID，以便下次运行继续补检。"
    )
    return 0 if send_email("ArXiv 当天更新检测结果", timeout_content) else 2


if __name__ == "__main__":
    raise SystemExit(main())
