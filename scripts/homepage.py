"""Build the GitHub Pages home page of a repo from its README.md and the doc-gen4 declarations.

usage: python3 homepage.py REPO_DIR OWNER/REPO DECL_JSON OUT_HTML

DECL_JSON is `docs/declarations/declaration-data.bmp` from the API documentation. The CI runs
this after doc-gen, so the home page follows the README on every push.
"""
import html, json, os, re, sys
import markdown

repo_dir, full_name, decl_path, out_path = sys.argv[1:5]
name = full_name.split("/")[-1]
gh = f"https://github.com/{full_name}"
decls = json.load(open(decl_path))["declarations"]

src = open(f"{repo_dir}/README.md").read()
lines = src.split("\n")
title = lines[0].lstrip("# ").strip()
tagline = lines[2].strip("* ")
# Drop title, tagline and the API documentation line: the header shows them.
body = "\n".join(l for l in lines[3:] if not l.startswith("API documentation"))

out = markdown.markdown(body, extensions=["tables", "fenced_code", "toc"])


def resolve(n):
    for cand in (f"LocallyConvex.Manifolds.{n}", f"LocallyConvex.Analysis.{n}", n):
        d = decls.get(cand)
        if d and "docLink" in d:
            return "docs/" + d["docLink"].removeprefix("./")
    return None


def link_code(m):
    inner = m.group(1)
    target = resolve(html.unescape(inner))
    if target:
        return f'<a class="decl" href="{target}"><code>{inner}</code></a>'
    return m.group(0)


# Link inline code that names a declaration, but not inside existing links or code blocks.
parts = re.split(r"(<a [^>]*>.*?</a>|<pre>.*?</pre>)", out, flags=re.S)
out = "".join(
    p if p.startswith(("<a ", "<pre>")) else re.sub(r"<code>([^<]+)</code>", link_code, p)
    for p in parts
)
# Relative links to files in the repository go to GitHub.
out = re.sub(r'href="((?:[A-Za-z]+/)*[A-Za-z]+\.lean|LICENSE|lakefile\.toml)"',
             lambda m: f'href="{gh}/blob/main/{m.group(1)}"', out)
out = out.replace('href="blueprint/src"', f'href="{gh}/tree/main/blueprint/src"')

# The blueprint, when the repository has one, is published next to the API documentation.
blueprint_links = ""
if os.path.isdir(f"{repo_dir}/blueprint"):
    blueprint_links = ('<a class="primary" href="blueprint/">Blueprint</a>\n'
                       '<a href="blueprint.pdf">Blueprint (PDF)</a>\n')

page = f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title}</title>
<meta name="description" content="{html.escape(tagline)}">
<style>
:root {{
  --bg: #fdfcf9; --fg: #1d1c1a; --muted: #5d5a54; --rule: #e4e0d8;
  --accent: #8a3b12; --code-bg: #f2efe8; --head-bg: #f6f3ec;
}}
@media (prefers-color-scheme: dark) {{
  :root:not([data-theme="light"]) {{
    --bg: #161514; --fg: #e9e6df; --muted: #a8a399; --rule: #34312c;
    --accent: #e39a6c; --code-bg: #24221f; --head-bg: #1d1c1a;
  }}
}}
:root[data-theme="dark"] {{
  --bg: #161514; --fg: #e9e6df; --muted: #a8a399; --rule: #34312c;
  --accent: #e39a6c; --code-bg: #24221f; --head-bg: #1d1c1a;
}}
* {{ box-sizing: border-box; }}
body {{ margin: 0; background: var(--bg); color: var(--fg);
  font: 17px/1.6 Charter, "Bitstream Charter", "Sitka Text", Cambria, Georgia, serif; }}
main, header > div {{ max-width: 860px; margin: 0 auto; padding: 0 16px; }}
header {{ background: var(--head-bg); border-bottom: 1px solid var(--rule); padding: 48px 0 32px; }}
h1 {{ font-size: 2.4rem; margin: 0 0 8px; letter-spacing: -0.01em; }}
.tagline {{ font-size: 1.2rem; color: var(--muted); margin: 0 0 24px; }}
.buttons {{ display: flex; flex-wrap: wrap; gap: 12px; }}
.buttons a {{ font: 600 15px/1 system-ui, sans-serif; text-decoration: none; padding: 11px 16px;
  border-radius: 6px; border: 1px solid var(--accent); color: var(--accent); }}
.buttons a.primary {{ background: var(--accent); color: var(--bg); }}
h2 {{ font-size: 1.6rem; margin: 2.2em 0 0.6em; padding-bottom: 6px; border-bottom: 1px solid var(--rule); }}
h3 {{ font-size: 1.2rem; margin: 1.8em 0 0.5em; }}
a {{ color: var(--accent); }}
code {{ font: 0.86em/1.4 ui-monospace, "SF Mono", Menlo, Consolas, monospace;
  background: var(--code-bg); padding: 1px 4px; border-radius: 3px; }}
a.decl {{ text-decoration: none; }}
a.decl code {{ border-bottom: 1px dotted var(--accent); }}
pre {{ background: var(--code-bg); padding: 14px 16px; border-radius: 6px; overflow-x: auto; }}
pre code {{ background: none; padding: 0; }}
blockquote {{ margin: 1em 0; padding: 4px 16px; border-left: 3px solid var(--accent); color: var(--muted); }}
table {{ border-collapse: collapse; width: 100%; font-size: 0.92em; display: block; overflow-x: auto; }}
th, td {{ text-align: left; vertical-align: top; padding: 8px 10px; border-bottom: 1px solid var(--rule); }}
th {{ font-family: system-ui, sans-serif; font-size: 0.85em; text-transform: uppercase;
  letter-spacing: 0.04em; color: var(--muted); }}
footer {{ max-width: 860px; margin: 48px auto 0; padding: 24px 16px 48px; color: var(--muted);
  border-top: 1px solid var(--rule); font-size: 0.9em; }}
@media (max-width: 600px) {{ body {{ font-size: 16px; }} h1 {{ font-size: 1.9rem; }} }}
</style>
</head>
<body>
<header><div>
<h1>{title}</h1>
<p class="tagline">{html.escape(tagline)}</p>
<div class="buttons">
<a class="primary" href="docs/">API documentation</a>
{blueprint_links}<a href="{gh}">Source on GitHub</a>
</div>
</div></header>
<main>
{out}
</main>
<footer>Names in <code>code</code> font link to their entry in the API documentation, generated by
<a href="https://github.com/leanprover/doc-gen4">doc-gen4</a>.</footer>
</body>
</html>
"""
open(out_path, "w").write(page)
print("ok", name, len(re.findall(r'class="decl"', out)), "declaration links")
