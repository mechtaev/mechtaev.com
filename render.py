from jinja2 import Environment, FileSystemLoader, select_autoescape
from markupsafe import Markup
import markdown as markdown_lib
import datetime
import json
import shutil
import os
from pathlib import Path

# Assumption: directory names coincide with page IDs
# Course pages with IDs are added dynamically in build() from data.json.
structure = {
    "overview": {
        "path": [],
        "template": "overview.html",
        "title": "Home"
    },
    "publications": {
        "path": ["publications"],
        "template": "publications.html",
        "title": "Publications"
    },
    "research": {
        "path": ["research"],
        "template": "research.html",
        "title": "Research"
    },
    "achievements": {
        "path": ["achievements"],
        "template": "achievements.html",
        "title": "Achievements"
    },
    "teaching": {
        "path": ["teaching"],
        "template": "teaching.html",
        "title": "Teaching",
        "render": False
    },
}

def page_url(id):
    url = "/"
    for d in structure[id]["path"]:
        url += d + "/"
    return url

def month_name(i):
    months = {
        1: "January",
        2: "February",
        3: "March",
        4: "April",
        5: "May",
        6: "June",
        7: "July",
        8: "August",
        9: "September",
        10: "October",
        11: "November",
        12: "December",
    }
    return months[i]

def weekday_name(date_obj):
    d = datetime.date(date_obj["year"], date_obj["month"], date_obj["day"])
    return d.strftime("%a")

env = Environment(
    loader = FileSystemLoader("templates"),
    autoescape = select_autoescape()
)

def file_url(file):
    return f"/files/{file}"

def include_markdown(filename):
    with open(Path("content") / filename, "r") as f:
        content = f.read()
    return Markup(markdown_lib.markdown(content))

env.globals["file_url"] = file_url
env.globals["page_url"] = page_url
env.globals["month_name"] = month_name
env.globals["include_markdown"] = include_markdown
env.globals["weekday_name"] = weekday_name

def render(output_dir, data):
    for id, config in structure.items():
        if not config.get("render", True):
            continue
        site_ctx = []
        for i, d in enumerate(config["path"]):
            path = "../" * (len(config["path"]) - i - 1)
            linked = structure[d].get("render", True)
            site_ctx.append((structure[d]["title"], path, linked))
        if site_ctx:
            site_ctx.insert(0, (structure["overview"]["title"], "../" + site_ctx[0][1], True))
            site_ctx.pop()
        page_data = data.copy()
        page_data["page_title"] = config["title"]
        page_data["page_context"] = []
        for t, p, linked in site_ctx:
            page_data["page_context"].append({ "title": t, "path": p, "linked": linked })
        if "course_id" in config:
            page_data["course"] = next(
                c for c in data["teaching"] if c.get("id") == config["course_id"]
            )
        template = env.get_template(config["template"])
        output_html = template.render(page_data)
        output_index_dir = output_dir
        for d in config["path"]:
            output_index_dir = output_index_dir / d
        output_index_dir.mkdir(parents=True, exist_ok=True)
        with open(output_index_dir / "index.html", "w") as file:
            file.write(output_html)


def build():
    def copy_dir_files(source_dir, destination_dir):
        if not os.path.exists(destination_dir):
            os.makedirs(destination_dir)
        for item in os.listdir(source_dir):
            source_item = os.path.join(source_dir, item)
            destination_item = os.path.join(destination_dir, item)
            if os.path.isfile(source_item):
                shutil.copy2(source_item, destination_item)
            elif os.path.isdir(source_item):
                shutil.copytree(source_item, destination_item, dirs_exist_ok=True)

    with open('data.json', 'r') as file:
        data = json.load(file)

    for course in data.get("teaching", []):
        if "id" in course:
            structure[course["id"]] = {
                "path": ["teaching", course["id"]],
                "template": "course.html",
                "title": course["title"],
                "course_id": course["id"]
            }

    output_dir = Path("_site")

    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    copy_dir_files("files", output_dir / "files")
    render(output_dir, data)


if __name__ == "__main__":
    build()
