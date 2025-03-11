import os
import re
import json
import difflib
import shutil
import numpy as np
from collections import defaultdict, Counter
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.metrics.pairwise import cosine_similarity

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
    
    def find_best_unknown_by_voting(self):
        """
        通过投票方式选出最佳的unknown文件
        
        每个sat/unsat文件对所有unknown文件评分，然后统计得分最高的unknown
        """
        if not self.unknown_files or (not self.sat_files and not self.unsat_files):
            print("没有足够的文件进行比较")
            return None
        
        # 准备文件列表
        unknown_files = list(self.unknown_files.keys())
        unknown_contents = [self.unknown_files[name] for name in unknown_files]
        
        # 准备参考文件列表
        reference_files = []
        reference_contents = []
        reference_types = []
        
        # 添加sat文件
        for name in self.sat_files:
            reference_files.append(name)
            reference_contents.append(self.sat_files[name])
            reference_types.append("sat")
            
        # 添加unsat文件
        for name in self.unsat_files:
            reference_files.append(name)
            reference_contents.append(self.unsat_files[name])
            reference_types.append("unsat")
            
        if not reference_files:
            print("没有sat/unsat文件作为参考")
            return None
        
        # 使用TF-IDF向量化所有文件
        all_contents = unknown_contents + reference_contents
        vectorizer = TfidfVectorizer(analyzer='word', token_pattern=r'\([^\)]+\)|\S+')
        
        try:
            tfidf_matrix = vectorizer.fit_transform(all_contents)
        except Exception as e:
            print(f"向量化文件内容时出错: {e}")
            return None
        
        # 计算相似度
        unknown_vectors = tfidf_matrix[:len(unknown_files)]
        reference_vectors = tfidf_matrix[len(unknown_files):]
        
        try:
            similarities = cosine_similarity(reference_vectors, unknown_vectors)
        except Exception as e:
            print(f"计算相似度时出错: {e}")
            return None
        
        # 每个reference文件投票给最相似的unknown文件
        votes = {}
        for i, ref_file in enumerate(reference_files):
            # 找出最相似的unknown文件
            best_unknown_idx = similarities[i].argmax()
            best_unknown = unknown_files[best_unknown_idx]
            similarity = similarities[i][best_unknown_idx]
            ref_type = reference_types[i]
            
            # 添加投票
            if best_unknown not in votes:
                votes[best_unknown] = {
                    "total_votes": 0,
                    "sat_votes": 0,
                    "unsat_votes": 0,
                    "total_similarity": 0,
                    "voters": []
                }
            
            votes[best_unknown]["total_votes"] += 1
            votes[best_unknown]["total_similarity"] += similarity
            votes[best_unknown][f"{ref_type}_votes"] += 1
            votes[best_unknown]["voters"].append({
                "file": ref_file,
                "type": ref_type,
                "similarity": similarity
            })
        
        # 如果没有任何投票，返回None
        if not votes:
            return None
        
        # 计算每个unknown的加权分数
        for unknown in votes:
            votes[unknown]["average_similarity"] = votes[unknown]["total_similarity"] / votes[unknown]["total_votes"]
            # 计算加权分数：总票数 * 平均相似度 * (较多类型的票数占比)
            dominant_votes = max(votes[unknown]["sat_votes"], votes[unknown]["unsat_votes"])
            dominant_ratio = dominant_votes / votes[unknown]["total_votes"] if votes[unknown]["total_votes"] > 0 else 0
            votes[unknown]["weighted_score"] = votes[unknown]["total_votes"] * votes[unknown]["average_similarity"] * (0.5 + 0.5 * dominant_ratio)
            
            # 确定主要类型
            votes[unknown]["primary_type"] = "sat" if votes[unknown]["sat_votes"] >= votes[unknown]["unsat_votes"] else "unsat"
        
        # 选出得分最高的unknown
        best_unknown = max(votes.items(), key=lambda x: x[1]["weighted_score"])
        
        return {
            "filename": best_unknown[0],
            "content": self.unknown_files[best_unknown[0]],
            "votes": best_unknown[1],
            "all_votes": votes
        }

def process_imo_results(imo_dir, collection_dir):
    """处理IMO_results目录下的所有问题文件夹，收集最具代表性的unknown文件"""
    print(f"处理IMO结果目录: {imo_dir}")
    print(f"将最佳unknown文件收集到: {collection_dir}")
    
    # 创建收集目录
    os.makedirs(collection_dir, exist_ok=True)
    
    
    results = {}
    problem_dirs = [d for d in os.listdir(imo_dir) if os.path.isdir(os.path.join(imo_dir, d)) and d.startswith('P')]
    
    for problem_dir in sorted(problem_dirs, key=lambda x: int(x[1:]) if x[1:].isdigit() else float('inf')):
        print(f"\n处理问题: {problem_dir}")
        problem_path = os.path.join(imo_dir, problem_dir)
        
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
        
        # 如果没有sat/unsat文件，跳过    
        if len(analyzer.sat_files) == 0 and len(analyzer.unsat_files) == 0:
            print(f"  跳过 {problem_dir} - 未找到sat/unsat文件")
            continue
            
        print(f"  找到 {len(analyzer.unknown_files)} 个unknown文件, {len(analyzer.sat_files)} 个sat文件, {len(analyzer.unsat_files)} 个unsat文件")
        
        # 通过投票选出最佳unknown文件
        best_unknown = analyzer.find_best_unknown_by_voting()
        if not best_unknown:
            print(f"  无法为 {problem_dir} 找到最佳unknown文件")
            continue
            
        print(f"  已为 {problem_dir} 选出最佳unknown文件: {best_unknown['filename']}")
        print(f"    获得 {best_unknown['votes']['total_votes']} 票，其中 {best_unknown['votes']['sat_votes']} 票来自sat，{best_unknown['votes']['unsat_votes']} 票来自unsat")
        
        # 保存最佳unknown到收集目录
        best_file = best_unknown["filename"]
        target_filename = f"{problem_dir}_{best_file}"
        target_path = os.path.join(collection_dir, target_filename)
        
        try:
            with open(target_path, 'w', encoding='utf-8') as f:
                f.write(best_unknown["content"])
            print(f"  已将最佳unknown文件 {best_file} 保存为 {target_filename}")
        except Exception as e:
            print(f"  警告: 无法保存文件 {target_path}: {e}")
            continue
        
        # 记录结果
        results[problem_dir] = {
            "best_unknown": best_unknown["filename"],
            "saved_as": target_filename,
            "total_votes": best_unknown["votes"]["total_votes"],
            "sat_votes": best_unknown["votes"]["sat_votes"],
            "unsat_votes": best_unknown["votes"]["unsat_votes"],
            "weighted_score": best_unknown["votes"]["weighted_score"],
            "primary_type": best_unknown["votes"]["primary_type"]
        }
        
    return results

def main():
    # 设置IMO结果的根目录
    imo_results_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "Evan_chen_results")
    
    if not os.path.exists(imo_results_dir):
        print(f"错误: 目录不存在 - {imo_results_dir}")
        print("请确保IMO_results目录位于脚本所在目录下")
        return
    
    # 设置收集目录
    collection_dir = os.path.join(imo_results_dir, "collected_unknowns")
    
    # 处理IMO结果目录下的所有问题，并收集最佳unknown
    results = process_imo_results(imo_results_dir, collection_dir)
    
    # 保存总的分析摘要
    output_summary_path = os.path.join(collection_dir, "collection_summary.json")
    with open(output_summary_path, 'w', encoding='utf-8') as f:
        json.dump(results, f, indent=2, ensure_ascii=False)
    
    # 打印总的分析摘要
    print("\n总分析摘要:")
    print(f"总共分析了 {len(results)} 个问题目录")
    print(f"已收集 {len(results)} 个最佳unknown文件到 {collection_dir}")
    
    # 统计不同类型的结果
    sat_primary = sum(1 for r in results.values() if r["primary_type"] == "sat")
    unsat_primary = sum(1 for r in results.values() if r["primary_type"] == "unsat")
    
    print(f"选出的最佳unknown文件中，有 {sat_primary} 个倾向于SAT，{unsat_primary} 个倾向于UNSAT")
    print(f"\n分析摘要已保存到 {output_summary_path}")

if __name__ == "__main__":
    main()