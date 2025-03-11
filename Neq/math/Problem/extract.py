import re

# 读取EVAN_CHAN.lean
with open("Evan_chen.lean", "r", encoding="utf-8") as f:
    content = f.read()

# 正则匹配每个theorem的第一行
theorem_lines = re.findall(r"theorem [^\n]+", content)

# 保存到文件或直接打印
with open("theorems_extracted.txt", "w", encoding="utf-8") as f:
    for line in theorem_lines:
        f.write(line + "\n")

print("提取完成，共找到", len(theorem_lines), "个theorem。")
