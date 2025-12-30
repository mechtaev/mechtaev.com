from jinja2 import Environment, FileSystemLoader, select_autoescape
import json
import shutil
import os
from pathlib import Path

# Assumption: directory names coincide with page IDs
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
    }
    # "group": {
    #     "path": ["group"],
    #     "template": "group.html",
    #     "title": "Group"
    # },
    # "vacancies": {
    #     "path": ["group", "vacancies"],
    #     "template": "vacancies.html",
    #     "title": "Vacancies"
    # },
    # "teaching": {
    #     "path": ["teaching"],
    #     "template": "teaching.html",
    #     "title": "Teaching"
    # },
    # "pku_softeng_24_25": {
    #     "path": ["teaching", "pku_softeng_24_25"],
    #     "template": "teaching.html",
    #     "title": "PKU 04834580 Software Engineering (Honor Track) 24-25"
    # }
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

env = Environment(
    loader = FileSystemLoader("templates"),
    autoescape = select_autoescape()
)

def file_url(file):
    return f"/files/{file}"

env.globals["file_url"] = file_url
env.globals["page_url"] = page_url
env.globals["month_name"] = month_name

def render(output_dir, data):
    for id, config in structure.items():
        site_ctx = []
        for i, d in enumerate(config["path"]):
            path = "../" * (len(config["path"]) - i - 1)
            site_ctx.append((structure[d]["title"], path))
        if site_ctx:
            site_ctx.insert(0, (structure["overview"]["title"], "../" + site_ctx[0][1]))
            site_ctx.pop()
        page_data = data.copy()
        page_data["page_title"] = config["title"]
        page_data["page_context"] = []
        for t, p in site_ctx:
            page_data["page_context"].append({ "title": t, "path": p })
        template = env.get_template(config["template"])
        output_html = template.render(page_data)
        output_index_dir = output_dir
        for d in config["path"]:
            output_index_dir = output_index_dir / d
        output_index_dir.mkdir(exist_ok=True)
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

    output_dir = Path("_site")

    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    copy_dir_files("files", output_dir / "files")
    render(output_dir, data)


if __name__ == "__main__":
    build()
