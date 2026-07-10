import json
import html
import os
from datetime import datetime

fullDir = "results/2026-03-24/moonshotai/Kimi-K2.5"
fullPath = os.path.join(fullDir, "results_2026-03-24_18-59-58_filtered.json")
output = {}
with open(fullPath, "r") as f:
        output = json.load(f)

# Start HTML content
html_content = """
    <!DOCTYPE html>
    <html lang="en">
    <head>
        <meta charset="UTF-8">
        <title>Coq Mechanization Review</title>
        <style>
            body { font-family: Arial, sans-serif; margin: 20px; }
            h2 { color: #2c3e50; }
            pre { background-color: #f4f4f4; padding: 10px; border-radius: 5px; overflow-x: auto; }
            .question { margin-bottom: 30px; }
            .answer { margin-top: 10px; background-color: #e8f5e9; padding: 10px; border-radius: 5px; }
        </style>
    </head>
    <body>
    <h1>Coq Mechanization Review Results</h1>
    """

# Loop through the results
for i, item in enumerate(output.get("results", []), start=1):
    question_html = html.escape(item.get("question", ""))
    answer_html = html.escape(str(item.get("answer") or ""))
    html_content += f"""
    <div class="question">
        <h2>Sample {i}</h2>
        <h3>Code / Comments:</h3>
        <pre>{question_html}</pre>
        <h3>Review / Answer:</h3>
        <div class="answer"><pre>{answer_html}</pre></div>
    </div>
    """

# Close HTML tags
html_content += """
</body>
</html>
"""

fullPath = os.path.join(fullDir, "results_2026-03-24_18-59-58_filtered.html")


# Write to file
with open(fullPath, "w", encoding="utf-8") as f:
    f.write(html_content)

print("HTML file 'review.html' created successfully.")
