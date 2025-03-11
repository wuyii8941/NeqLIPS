import os
import re
import json
import shutil
from glob import glob
from pathlib import Path

def extract_latest_unknown_smt_files(base_dir, output_dir):
    """
    Extract the latest step's SMT file from each problem's 'unknown' verification steps folder.
    
    Args:
        base_dir (str): Base directory containing problem folders (P1, P2, ...)
        output_dir (str): Directory where the extracted SMT files will be saved
    """
    # Create output directory if it doesn't exist
    os.makedirs(output_dir, exist_ok=True)
    
    # Find all problem folders (P1, P2, ...)
    problem_dirs = sorted([d for d in os.listdir(base_dir) 
                   if os.path.isdir(os.path.join(base_dir, d)) and d.startswith('P')])
    
    print(f"Found {len(problem_dirs)} problem directories")
    
    # List to store files for sequential numbering
    smt_files = []
    
    for problem_dir in problem_dirs:
        problem_path = os.path.join(base_dir, problem_dir)
        unknown_dir = os.path.join(problem_path, 'verification_steps', 'unknown')
        
        if not os.path.exists(unknown_dir):
            print(f"Skipping {problem_dir}: No 'unknown' directory found")
            continue
            
        # Find all json files in the unknown directory
        json_files = glob(os.path.join(unknown_dir, 'step_*.json'))
        
        if not json_files:
            print(f"Skipping {problem_dir}: No step files found in 'unknown' directory")
            continue
        
        # Extract step numbers and find the largest (latest) one
        step_numbers = []
        for json_file in json_files:
            match = re.search(r'step_(\d+)\.json', json_file)
            if match:
                step_numbers.append(int(match.group(1)))
        
        if not step_numbers:
            print(f"Skipping {problem_dir}: Could not extract step numbers")
            continue
            
        latest_step = max(step_numbers)
        latest_json = os.path.join(unknown_dir, f'step_{latest_step}.json')
        latest_smt = os.path.join(unknown_dir, f'step_{latest_step}.smt2')
        
        # Check if corresponding SMT file exists
        if not os.path.exists(latest_smt):
            print(f"Skipping {problem_dir}: SMT file for latest step {latest_step} not found")
            continue
        
        # Read the JSON file to get additional info (optional)
        try:
            with open(latest_json, 'r', encoding='utf-8') as f:
                step_data = json.load(f)
                step_id = step_data.get('step_id', latest_step)
        except Exception as e:
            print(f"Warning: Could not read JSON for {problem_dir}, step {latest_step}: {e}")
            step_id = latest_step
        
        # Add to collection for sequential numbering
        smt_files.append({
            'problem': problem_dir,
            'step_id': step_id,
            'source_path': latest_smt
        })
    
    # Copy files with sequential naming
    for i, file_info in enumerate(smt_files, 1):
        output_file = os.path.join(output_dir, f"unknown_{i:03d}.smt2")
        shutil.copy2(file_info['source_path'], output_file)
        print(f"Copied {file_info['problem']}'s unknown SMT (step {file_info['step_id']}) to {output_file}")
        
        # Optionally create a mapping file to keep track of original sources
        with open(os.path.join(output_dir, "file_mapping.txt"), "a") as f:
            f.write(f"unknown_{i:03d}.smt2: {file_info['problem']}_step_{file_info['step_id']}\n")
    
    # Count extracted files
    print(f"\nExtraction complete. {len(smt_files)} SMT files extracted to {output_dir}")


if __name__ == "__main__":
    # Set your output directory
    output_directory = "collected_unknown_dataset"  # Output folder name
    
    # Clear mapping file if it exists
    mapping_file = os.path.join(output_directory, "file_mapping.txt")
    if os.path.exists(mapping_file):
        os.remove(mapping_file)
    
    # Process both IMO_results and Evan_chen_results
    base_directories = ["IMO_results", "Evan_chen_results"]
    
    # List to store all SMT files from both directories
    all_smt_files = []
    
    # Process each base directory
    for base_dir in base_directories:
        if not os.path.exists(base_dir):
            print(f"Warning: Directory {base_dir} does not exist. Skipping.")
            continue
            
        print(f"\nProcessing directory: {base_dir}")
        
        # Extract SMT files but don't copy them yet - just collect information
        def collect_smt_files(base_dir, output_dir):
            collected_files = []
            
            # Find all problem folders (P1, P2, ...)
            problem_dirs = sorted([d for d in os.listdir(base_dir) 
                           if os.path.isdir(os.path.join(base_dir, d)) and d.startswith('P')])
            
            print(f"Found {len(problem_dirs)} problem directories in {base_dir}")
            
            for problem_dir in problem_dirs:
                problem_path = os.path.join(base_dir, problem_dir)
                unknown_dir = os.path.join(problem_path, 'verification_steps', 'unknown')
                
                if not os.path.exists(unknown_dir):
                    print(f"Skipping {problem_dir}: No 'unknown' directory found")
                    continue
                    
                # Find all json files in the unknown directory
                json_files = glob(os.path.join(unknown_dir, 'step_*.json'))
                
                if not json_files:
                    print(f"Skipping {problem_dir}: No step files found in 'unknown' directory")
                    continue
                
                # Extract step numbers and find the largest (latest) one
                step_numbers = []
                for json_file in json_files:
                    match = re.search(r'step_(\d+)\.json', json_file)
                    if match:
                        step_numbers.append(int(match.group(1)))
                
                if not step_numbers:
                    print(f"Skipping {problem_dir}: Could not extract step numbers")
                    continue
                    
                latest_step = max(step_numbers)
                latest_json = os.path.join(unknown_dir, f'step_{latest_step}.json')
                latest_smt = os.path.join(unknown_dir, f'step_{latest_step}.smt2')
                
                # Check if corresponding SMT file exists
                if not os.path.exists(latest_smt):
                    print(f"Skipping {problem_dir}: SMT file for latest step {latest_step} not found")
                    continue
                
                # Read the JSON file to get additional info (optional)
                try:
                    with open(latest_json, 'r', encoding='utf-8') as f:
                        step_data = json.load(f)
                        step_id = step_data.get('step_id', latest_step)
                except Exception as e:
                    print(f"Warning: Could not read JSON for {problem_dir}, step {latest_step}: {e}")
                    step_id = latest_step
                
                # Add to collection
                collected_files.append({
                    'problem': f"{base_dir}_{problem_dir}",  # Include source directory in problem ID
                    'step_id': step_id,
                    'source_path': latest_smt
                })
                
            return collected_files
        
        # Collect SMT files from current directory
        dir_smt_files = collect_smt_files(base_dir, output_directory)
        all_smt_files.extend(dir_smt_files)
    
    # Create output directory if it doesn't exist
    os.makedirs(output_directory, exist_ok=True)
    
    # Copy all collected files with sequential naming
    for i, file_info in enumerate(all_smt_files, 1):
        output_file = os.path.join(output_directory, f"unknown_{i:03d}.smt2")
        shutil.copy2(file_info['source_path'], output_file)
        print(f"Copied {file_info['problem']}'s unknown SMT (step {file_info['step_id']}) to {output_file}")
        
        # Create a mapping file to keep track of original sources
        with open(os.path.join(output_directory, "file_mapping.txt"), "a") as f:
            f.write(f"unknown_{i:03d}.smt2: {file_info['problem']}_step_{file_info['step_id']}\n")
    
    # Print summary
    print(f"\nExtraction complete. {len(all_smt_files)} SMT files extracted to {output_directory}")