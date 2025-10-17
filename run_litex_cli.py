#!/usr/bin/env python3
import os
import re
import subprocess
import time
import json
from datetime import datetime

startTime = time.time()

folder_path = "./Tutorial"

# 匹配 ```litex ... ```
pattern = re.compile(r"```litex\s*(.*?)```", re.DOTALL)

total_blocks = 0
failed_blocks = 0
failed_details = []

for root, _, files in os.walk(folder_path):
    for file in sorted(files):
        if file.endswith(".md"):
            file_path = os.path.join(root, file)
            with open(file_path, "r", encoding="utf-8") as f:
                content = f.read()

                matches = pattern.findall(content)
                if matches:
                    for i, code_block in enumerate(matches, start=1):
                        total_blocks += 1
                        # 使用 litex -e 运行代码
                        try:
                            result = subprocess.run(
                                ["litex", "-e", code_block],
                                capture_output=True,
                                text=True,
                                timeout=30  # 30秒超时
                            )
                            
                            # 检查返回码
                            if result.returncode != 0:
                                failed_blocks += 1
                                failed_details.append({
                                    'file': file_path,
                                    'block_num': i,
                                    'code': code_block,
                                    'stdout': result.stdout,
                                    'stderr': result.stderr,
                                    'returncode': result.returncode
                                })
                                print(f"❌ Failed: {file_path} (block {i})")
                            else:
                                print(f"✓ Passed: {file_path} (block {i})")
                                
                        except subprocess.TimeoutExpired:
                            failed_blocks += 1
                            failed_details.append({
                                'file': file_path,
                                'block_num': i,
                                'code': code_block,
                                'stdout': '',
                                'stderr': 'Timeout (30s)',
                                'returncode': -1
                            })
                            print(f"⏱ Timeout: {file_path} (block {i})")
                        except Exception as e:
                            failed_blocks += 1
                            failed_details.append({
                                'file': file_path,
                                'block_num': i,
                                'code': code_block,
                                'stdout': '',
                                'stderr': str(e),
                                'returncode': -1
                            })
                            print(f"💥 Error: {file_path} (block {i}): {e}")

endTime = time.time()

print("\n" + "="*80)
print(f"Total blocks: {total_blocks}")
print(f"Passed: {total_blocks - failed_blocks}")
print(f"Failed: {failed_blocks}")
print(f"Time taken: {endTime - startTime:.2f} seconds")

# 保存测试结果到文件
report_data = {
    'timestamp': datetime.now().isoformat(),
    'total_blocks': total_blocks,
    'passed': total_blocks - failed_blocks,
    'failed': failed_blocks,
    'time_taken': f"{endTime - startTime:.2f}s",
    'failed_details': failed_details
}

# 保存JSON格式（方便程序读取）
with open('litex_test_report.json', 'w', encoding='utf-8') as f:
    json.dump(report_data, f, indent=2, ensure_ascii=False)

# 保存文本格式（方便人类阅读）
with open('litex_test_report.txt', 'w', encoding='utf-8') as f:
    f.write(f"Litex代码测试报告\n")
    f.write(f"测试时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
    f.write(f"{'='*80}\n\n")
    f.write(f"总代码块数: {total_blocks}\n")
    f.write(f"通过: {total_blocks - failed_blocks}\n")
    f.write(f"失败: {failed_blocks}\n")
    f.write(f"耗时: {endTime - startTime:.2f}秒\n\n")
    
    if failed_blocks > 0:
        f.write(f"{'='*80}\n")
        f.write(f"失败详情:\n")
        f.write(f"{'='*80}\n\n")
        for i, detail in enumerate(failed_details, 1):
            f.write(f"{i}. 文件: {detail['file']}\n")
            f.write(f"   代码块编号: {detail['block_num']}\n")
            f.write(f"   返回码: {detail['returncode']}\n")
            f.write(f"\n   代码:\n")
            f.write(f"   {'-'*40}\n")
            for line in detail['code'].split('\n'):
                f.write(f"   {line}\n")
            f.write(f"   {'-'*40}\n")
            if detail['stdout']:
                f.write(f"\n   标准输出:\n")
                for line in detail['stdout'].split('\n'):
                    f.write(f"   {line}\n")
            if detail['stderr']:
                f.write(f"\n   错误信息:\n")
                for line in detail['stderr'].split('\n')[:20]:  # 只显示前20行错误
                    f.write(f"   {line}\n")
                if len(detail['stderr'].split('\n')) > 20:
                    f.write(f"   ...(错误信息过长，已截断)\n")
            f.write(f"\n{'='*80}\n\n")

if failed_blocks > 0:
    print("\n" + "="*80)
    print("FAILED BLOCKS DETAILS:")
    print("="*80)
    for detail in failed_details:
        print(f"\n📁 File: {detail['file']}")
        print(f"🔢 Block: {detail['block_num']}")
        print(f"📝 Code:")
        print("-" * 40)
        print(detail['code'])
        print("-" * 40)
        if detail['stdout']:
            print(f"📤 STDOUT:")
            print(detail['stdout'])
        if detail['stderr']:
            print(f"📤 STDERR:")
            print(detail['stderr'])
        print(f"↩️  Return code: {detail['returncode']}")
        print("="*80)
    
    print(f"\n📝 测试报告已保存到:")
    print(f"   - litex_test_report.txt (文本格式)")
    print(f"   - litex_test_report.json (JSON格式)")
    exit(1)
else:
    print("\n✅ All litex code blocks passed!")
    print(f"\n📝 测试报告已保存到:")
    print(f"   - litex_test_report.txt (文本格式)")
    print(f"   - litex_test_report.json (JSON格式)")
    exit(0)

