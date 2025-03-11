import os
import subprocess
import sys

# 读取theorems_extracted.txt
theorems_path = "Neq/math/Problem/theorems_extracted.txt"
print(f"正在读取 {theorems_path}")

with open(theorems_path, "r", encoding="utf-8") as f:
    theorems = [line.strip() for line in f.readlines() if line.strip()]

print(f"共发现 {len(theorems)} 个定理需要处理\n")

# 结果保存目录
output_base = "Evan_chen_results"
# output_base = "IMO_results"
os.makedirs(output_base, exist_ok=True)

def run_prove_with_realtime_output(cmd, log_path, env=None):
    """实时执行prove.py，并同步输出到屏幕和日志文件"""
    with open(log_path, "w", encoding="utf-8") as log_file:
        process = subprocess.Popen(
            cmd,
            shell=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,  # 合并stderr到stdout
            text=True,
            env=env,
            bufsize=1  # 行缓冲，实时刷新
        )

        # 逐行读取，实时打印并写日志
        while True:
            line = process.stdout.readline()
            if not line and process.poll() is not None:
                break
            if line:
                print(line, end="")  # 实时输出到屏幕
                log_file.write(line)  # 同步保存到日志文件
                log_file.flush()  # 立即写盘，避免缓存

        # 确保读取完所有剩余输出
        remaining = process.stdout.read()
        if remaining:
            print(remaining, end="")
            log_file.write(remaining)
            log_file.flush()

        return process.returncode

for index, theorem_text in enumerate(theorems, start=1):
    # 获取编号，例如P1、P2
    theorem_id = theorem_text.split()[1]

    # 创建该定理的保存目录
    theorem_dir = os.path.join(output_base, theorem_id)
    os.makedirs(theorem_dir, exist_ok=True)

    # 拼接完整的命令行参数（加上 := by sorry）
    full_problem = f'{theorem_text}  sorry'

    # 设置环境变量，把session_id传给scaler
    env = os.environ.copy()
    env["SCALER_SESSION_ID"] = theorem_id  # 让scaler保存时带上P1、P2的编号

    # 日志路径
    log_path = os.path.join(theorem_dir, "prove_log.txt")

    # 开始处理当前theorem
    print(f"[{index}/{len(theorems)}] 开始处理 {theorem_id} ...")

    # 调用prove.py，实时输出+写日志
    cmd = f'python prove.py --problem "{full_problem}"'
    print(f"执行命令: {cmd}")
    returncode = run_prove_with_realtime_output(cmd, log_path, env=env)

    # 处理完成
    if returncode == 0:
        print(f"{theorem_id} 处理完成\n")
    else:
        print(f"{theorem_id} 处理失败，请查看 {log_path}\n")

print(f"全部定理处理完成，结果已保存到：{output_base}\n")