import os
import re
import json
import difflib
import shutil
import numpy as np
from collections import defaultdict, Counter

class SMTAnalyzer:
    def __init__(self, base_dir):
        """
        初始化SMT分析器
        
        Args:
            base_dir: 验证步骤的根目录
        """
        self.base_dir = base_dir
        self.unknown_dir = os.path.join(base_dir, "unknown")
        self.sat_dir = os.path.join(base_dir, "sat")
        self.unsat_dir = os.path.join(base_dir, "unsat")
        
        # 检查目录是否存在
        for dir_path in [self.unknown_dir, self.sat_dir, self.unsat_dir]:
            if not os.path.exists(dir_path):
                print(f"警告: 目录 {dir_path} 不存在")
        
        # 存储加载的文件内容
        self.unknown_files = {}
        self.sat_files = {}
        self.unsat_files = {}
        
        # 加载所有SMT文件
        self._load_all_files()
        
    def _load_all_files(self):
        """加载所有SMT文件内容"""
        print("加载SMT文件...")
        
        # 加载unknown文件
        if os.path.exists(self.unknown_dir):
            for filename in [f for f in os.listdir(self.unknown_dir) if f.endswith('.smt2')]:
                file_path = os.path.join(self.unknown_dir, filename)
                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        self.unknown_files[filename] = f.read()
                except Exception as e:
                    print(f"警告: 无法读取文件 {file_path}: {e}")
        
        # 加载sat文件
        if os.path.exists(self.sat_dir):
            for filename in [f for f in os.listdir(self.sat_dir) if f.endswith('.smt2')]:
                file_path = os.path.join(self.sat_dir, filename)
                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        self.sat_files[filename] = f.read()
                except Exception as e:
                    print(f"警告: 无法读取文件 {file_path}: {e}")
        
        # 加载unsat文件
        if os.path.exists(self.unsat_dir):
            for filename in [f for f in os.listdir(self.unsat_dir) if f.endswith('.smt2')]:
                file_path = os.path.join(self.unsat_dir, filename)
                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        self.unsat_files[filename] = f.read()
                except Exception as e:
                    print(f"警告: 无法读取文件 {file_path}: {e}")
        
        print(f"已加载 {len(self.unknown_files)} 个unknown文件, {len(self.sat_files)} 个sat文件, {len(self.unsat_files)} 个unsat文件")
    
    def calculate_complexity(self, smt_content):
        """
        计算SMT文件的复杂度
        
        这里使用多个指标来确定文件的复杂度:
        1. 总行数
        2. declare-const 和 declare-fun 的数量
        3. assert 语句的数量
        4. 表达式的嵌套深度
        5. 文件总字符数
        
        Returns:
            复杂度分数 (越低表示越简单)
        """
        # 1. 计算总行数
        lines = smt_content.strip().split('\n')
        line_count = len(lines)
        
        # 2. 计算声明的数量
        declare_count = smt_content.count('declare-const') + smt_content.count('declare-fun')
        
        # 3. 计算断言的数量
        assert_count = smt_content.count('assert')
        
        # 4. 估计表达式的嵌套深度
        # 通过计算括号的最大嵌套深度来估计
        max_depth = 0
        current_depth = 0
        for char in smt_content:
            if char == '(':
                current_depth += 1
                max_depth = max(max_depth, current_depth)
            elif char == ')':
                current_depth = max(0, current_depth - 1)
        
        # 5. 文件总字符数
        char_count = len(smt_content)
        
        # 计算总体复杂度分数
        # 这里使用简单的加权和，可以根据需要调整权重
        complexity_score = (
            0.2 * line_count + 
            0.2 * declare_count + 
            0.2 * assert_count + 
            0.2 * max_depth + 
            0.2 * (char_count / 100)  # 除以100使其量级与其他指标相近
        )
        
        return complexity_score
    
    def find_simplest_unknown(self):
        """
        找出结构最简单的unknown文件
        
        Returns:
            包含文件名和内容的字典，如果没有文件则返回None
        """
        if not self.unknown_files:
            print("没有可用的unknown文件")
            return None
        
        # 计算每个文件的复杂度
        complexities = {}
        for filename, content in self.unknown_files.items():
            try:
                complexity = self.calculate_complexity(content)
                complexities[filename] = complexity
            except Exception as e:
                print(f"计算 {filename} 的复杂度时出错: {e}")
                complexities[filename] = float('inf')  # 设置为无穷大，这样它不会被选中
        
        # 找出复杂度最低的文件
        simplest_file = min(complexities.items(), key=lambda x: x[1])
        
        return {
            "filename": simplest_file[0],
            "content": self.unknown_files[simplest_file[0]],
            "complexity": simplest_file[1],
            "all_complexities": complexities
        }

def process_results(source_dir, collection_dir, source_name):
    """处理结果目录下的所有问题文件夹，收集最简单的unknown文件
    
    Args:
        source_dir: 源目录
        collection_dir: 收集目录
        source_name: 源名称（用于区分不同来源的文件）
    """
    print(f"处理{source_name}结果目录: {source_dir}")
    print(f"将最简单的unknown文件收集到: {collection_dir}")
    
    # 创建特定来源的收集子目录
    source_collection_dir = os.path.join(collection_dir, source_name)
    os.makedirs(source_collection_dir, exist_ok=True)
    
    results = {}
    
    # 检查源目录是否存在
    if not os.path.exists(source_dir):
        print(f"警告: 源目录不存在 - {source_dir}")
        return results
    
    # 获取所有问题目录，包括可能有前导零的情况（如P01, P1等）
    problem_dirs = []
    for item in os.listdir(source_dir):
        item_path = os.path.join(source_dir, item)
        if os.path.isdir(item_path) and item.startswith('P'):
            # 尝试提取数字部分
            num_part = item[1:]
            if num_part.isdigit():
                problem_dirs.append((item, int(num_part)))
    
    # 按数字排序
    problem_dirs.sort(key=lambda x: x[1])
    sorted_problem_dirs = [dir_name for dir_name, _ in problem_dirs]
    
    print(f"找到 {len(sorted_problem_dirs)} 个问题目录")
    
    for problem_dir in sorted_problem_dirs:
        print(f"\n处理问题: {problem_dir}")
        problem_path = os.path.join(source_dir, problem_dir)
        
        # 检查验证步骤目录是否存在
        verification_path = os.path.join(problem_path, "verification_steps")
        if not os.path.exists(verification_path):
            print(f"  跳过 {problem_dir} - 未找到验证步骤目录")
            continue
            
        # 创建SMT分析器
        analyzer = SMTAnalyzer(verification_path)
        
        # 如果没有unknown文件，跳过
        if len(analyzer.unknown_files) == 0:
            print(f"  跳过 {problem_dir} - 未找到unknown文件")
            continue
            
        print(f"  找到 {len(analyzer.unknown_files)} 个unknown文件")
        
        # 选出最简单的unknown文件
        simplest_unknown = analyzer.find_simplest_unknown()
        if not simplest_unknown:
            print(f"  无法为 {problem_dir} 找到unknown文件")
            continue
            
        print(f"  已为 {problem_dir} 选出最简单的unknown文件: {simplest_unknown['filename']}")
        print(f"    复杂度分数: {simplest_unknown['complexity']:.2f}")
        
        # 保存最简单的unknown到特定来源的收集目录
        best_file = simplest_unknown["filename"]
        target_filename = f"{problem_dir}_{best_file}"
        target_path = os.path.join(source_collection_dir, target_filename)
        
        try:
            with open(target_path, 'w', encoding='utf-8') as f:
                f.write(simplest_unknown["content"])
            print(f"  已将最简单的unknown文件 {best_file} 保存为 {target_filename} 到 {source_name} 目录")
        except Exception as e:
            print(f"  警告: 无法保存文件 {target_path}: {e}")
            continue
        
        # 记录结果
        results[problem_dir] = {
            "simplest_unknown": simplest_unknown["filename"],
            "saved_as": target_filename,
            "complexity": simplest_unknown["complexity"],
            "total_files": len(analyzer.unknown_files)
        }
    
    # 为每个来源保存单独的摘要
    output_summary_path = os.path.join(source_collection_dir, f"{source_name}_summary.json")
    with open(output_summary_path, 'w', encoding='utf-8') as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
    
    print(f"\n{source_name}分析摘要:")
    print(f"总共分析了 {len(sorted_problem_dirs)} 个问题目录")
    print(f"已收集 {len(results)} 个最简单的unknown文件到 {source_collection_dir}")
    print(f"\n{source_name}分析摘要已保存到 {output_summary_path}")
    
    return results

def main():
    # 获取当前脚本所在目录的路径
    script_dir = os.path.dirname(os.path.abspath(__file__))
    
    # 设置结果的根目录
    evan_chen_dir = os.path.join(script_dir, "Evan_chen_results")
    imo_dir = os.path.join(script_dir, "IMO_results")
    
    # 设置收集总目录
    collection_dir = os.path.join(script_dir, "collected_unknowns")
    os.makedirs(collection_dir, exist_ok=True)
    
    all_results = {}
    
    # 处理Evan Chen结果
    if os.path.exists(evan_chen_dir):
        evan_chen_results = process_results(evan_chen_dir, collection_dir, "evan_chen")
        all_results["evan_chen"] = evan_chen_results
    else:
        print(f"警告: 目录不存在 - {evan_chen_dir}")
    
    # 处理IMO结果
    if os.path.exists(imo_dir):
        imo_results = process_results(imo_dir, collection_dir, "imo")
        all_results["imo"] = imo_results
    else:
        print(f"警告: 目录不存在 - {imo_dir}")
    
    # 保存总体分析摘要
    output_summary_path = os.path.join(collection_dir, "collection_summary.json")
    with open(output_summary_path, 'w', encoding='utf-8') as f:
        json.dump(all_results, f, indent=2, ensure_ascii=False)
    
    # 打印总体分析摘要
    print("\n总分析摘要:")
    total_problems = sum(len(results) for results in all_results.values())
    print(f"总共分析了 {len(all_results.keys())} 个数据集中的 {total_problems} 个问题目录")
    
    # 统计不同来源的结果数量
    for source, results in all_results.items():
        source_dir = os.path.join(collection_dir, source)
        print(f"- {source}: 收集了 {len(results)} 个最简单的unknown文件到 {source_dir}")
    
    print(f"\n总分析摘要已保存到 {output_summary_path}")

if __name__ == "__main__":
    main()