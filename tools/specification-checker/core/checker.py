"""
SystemOSIOT 规范检查器核心实现

该模块实现了规范检查器的核心功能，包括：
1. 规范加载和解析
2. 多维度检查
3. 结果整合
4. 报告生成
"""

from typing import Dict, List, Any, Optional
from dataclasses import dataclass
import logging
import json
import time
from pathlib import Path

from ..languages.system_lang import SystemTheoryLanguage
from ..algorithms.consistency import ConsistencyChecker

@dataclass
class CheckResult:
    """检查结果"""
    success: bool
    errors: List[str]
    warnings: List[str]
    details: Dict[str, Any]
    execution_time: float

class SpecificationChecker:
    """规范检查器主类"""
    
    def __init__(self):
        self.logger = logging.getLogger(__name__)
        self.language = SystemTheoryLanguage()
        self.consistency_checker = ConsistencyChecker()
        
    def check_specification(self, spec_path: str) -> CheckResult:
        """检查规范文件"""
        start_time = time.time()
        
        try:
            # 加载规范文件
            spec_content = self._load_specification(spec_path)
            
            # 解析规范
            parse_result = self.language.check_syntax(spec_content)
            
            if not parse_result["valid"]:
                return CheckResult(
                    success=False,
                    errors=parse_result["errors"],
                    warnings=[],
                    details={"parse_errors": len(parse_result["errors"])},
                    execution_time=time.time() - start_time
                )
            
            # 执行一致性检查
            consistency_result = self.consistency_checker.check_all(
                self._parse_to_dict(parse_result["ast"])
            )
            
            # 整合结果
            result = CheckResult(
                success=consistency_result.is_consistent,
                errors=consistency_result.errors,
                warnings=consistency_result.warnings,
                details=consistency_result.details,
                execution_time=time.time() - start_time
            )
            
            return result
            
        except Exception as e:
            self.logger.error(f"检查过程中发生错误: {e}")
            return CheckResult(
                success=False,
                errors=[f"检查错误: {str(e)}"],
                warnings=[],
                details={},
                execution_time=time.time() - start_time
            )
    
    def _load_specification(self, spec_path: str) -> str:
        """加载规范文件"""
        path = Path(spec_path)
        if not path.exists():
            raise FileNotFoundError(f"规范文件不存在: {spec_path}")
        
        with open(path, 'r', encoding='utf-8') as f:
            return f.read()
    
    def _parse_to_dict(self, ast) -> Dict[str, Any]:
        """将AST转换为字典格式"""
        # 简化的AST到字典转换
        return {
            "systems": [],
            "axioms": [],
            "theorems": []
        }
    
    def generate_report(self, result: CheckResult, output_path: str):
        """生成检查报告"""
        report = {
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "success": result.success,
            "execution_time": f"{result.execution_time:.2f}s",
            "summary": {
                "total_errors": len(result.errors),
                "total_warnings": len(result.warnings)
            },
            "errors": result.errors,
            "warnings": result.warnings,
            "details": result.details
        }
        
        # 保存JSON报告
        json_path = Path(output_path).with_suffix('.json')
        with open(json_path, 'w', encoding='utf-8') as f:
            json.dump(report, f, indent=2, ensure_ascii=False)
        
        # 生成HTML报告
        html_path = Path(output_path).with_suffix('.html')
        self._generate_html_report(report, html_path)
        
        self.logger.info(f"报告已生成: {json_path}, {html_path}")
    
    def _generate_html_report(self, report: Dict[str, Any], output_path: Path):
        """生成HTML报告"""
        html_content = f"""
<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <title>SystemOSIOT 规范检查报告</title>
    <style>
        body {{ font-family: Arial, sans-serif; margin: 20px; }}
        .header {{ background-color: #f0f0f0; padding: 20px; border-radius: 5px; }}
        .success {{ color: green; }}
        .error {{ color: red; }}
        .warning {{ color: orange; }}
        .section {{ margin: 20px 0; }}
        .details {{ background-color: #f9f9f9; padding: 10px; border-radius: 3px; }}
    </style>
</head>
<body>
    <div class="header">
        <h1>SystemOSIOT 规范检查报告</h1>
        <p>检查时间: {report['timestamp']}</p>
        <p>执行时间: {report['execution_time']}</p>
        <p>检查结果: <span class="{'success' if report['success'] else 'error'}">
            {'通过' if report['success'] else '失败'}
        </span></p>
    </div>
    
    <div class="section">
        <h2>检查摘要</h2>
        <p>错误数量: <span class="error">{report['summary']['total_errors']}</span></p>
        <p>警告数量: <span class="warning">{report['summary']['total_warnings']}</span></p>
    </div>
"""
        
        if report['errors']:
            html_content += """
    <div class="section">
        <h2>错误详情</h2>
        <ul>
"""
            for error in report['errors']:
                html_content += f"            <li class='error'>{error}</li>\n"
            html_content += "        </ul>\n    </div>\n"
        
        if report['warnings']:
            html_content += """
    <div class="section">
        <h2>警告详情</h2>
        <ul>
"""
            for warning in report['warnings']:
                html_content += f"            <li class='warning'>{warning}</li>\n"
            html_content += "        </ul>\n    </div>\n"
        
        if report['details']:
            html_content += """
    <div class="section">
        <h2>详细信息</h2>
        <div class="details">
"""
            for key, value in report['details'].items():
                html_content += f"            <p><strong>{key}:</strong> {value}</p>\n"
            html_content += "        </div>\n    </div>\n"
        
        html_content += """
</body>
</html>
"""
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html_content)

def main():
    """主函数"""
    checker = SpecificationChecker()
    
    # 示例用法
    spec_file = "example.spec"
    result = checker.check_specification(spec_file)
    
    print("=== 规范检查结果 ===")
    print(f"检查成功: {'是' if result.success else '否'}")
    print(f"执行时间: {result.execution_time:.2f}秒")
    print(f"错误数量: {len(result.errors)}")
    print(f"警告数量: {len(result.warnings)}")
    
    if result.errors:
        print("\n错误:")
        for error in result.errors:
            print(f"  - {error}")
    
    if result.warnings:
        print("\n警告:")
        for warning in result.warnings:
            print(f"  - {warning}")
    
    # 生成报告
    checker.generate_report(result, "check_report")

if __name__ == "__main__":
    main()
