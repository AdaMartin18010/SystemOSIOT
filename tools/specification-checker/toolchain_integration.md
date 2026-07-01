# SystemOSIOT 工具链集成指南

## 📋 概述

本文档描述了如何将SystemOSIOT形式化规范检查工具与其他工具进行集成，构建完整的系统理论验证工具链。

## 🔗 工具链架构

### 集成架构图

```text
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   规范编辑器    │    │   规范检查器    │    │   验证工具      │
│   (Editor)      │───▶│   (Checker)     │───▶│   (Verifier)    │
└─────────────────┘    └─────────────────┘    └─────────────────┘
         │                       │                       │
         ▼                       ▼                       ▼
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   语法高亮      │    │   错误诊断      │    │   证明生成      │
│   (Syntax)      │    │   (Diagnostic)  │    │   (Proof)       │
└─────────────────┘    └─────────────────┘    └─────────────────┘
         │                       │                       │
         ▼                       ▼                       ▼
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│   自动补全      │    │   报告生成      │    │   测试框架      │
│   (Completion)  │    │   (Reporter)    │    │   (Testing)     │
└─────────────────┘    └─────────────────┘    └─────────────────┘
```

## 🛠️ 集成接口

### 1. 与Coq验证工具集成

```python
# tools/specification-checker/integrations/coq_integration.py

from typing import Dict, Any
import subprocess
import tempfile
import os

class CoqIntegration:
    """Coq验证工具集成"""

    def __init__(self, coq_path: str = "coqc"):
        self.coq_path = coq_path

    def verify_specification(self, spec_dict: Dict[str, Any]) -> Dict[str, Any]:
        """验证规范"""
        # 生成Coq代码
        coq_code = self._generate_coq_code(spec_dict)

        # 写入临时文件
        with tempfile.NamedTemporaryFile(mode='w', suffix='.v', delete=False) as f:
            f.write(coq_code)
            temp_file = f.name

        try:
            # 执行Coq验证
            result = subprocess.run(
                [self.coq_path, temp_file],
                capture_output=True,
                text=True,
                timeout=30
            )

            return {
                "success": result.returncode == 0,
                "output": result.stdout,
                "errors": result.stderr,
                "coq_code": coq_code
            }

        finally:
            # 清理临时文件
            os.unlink(temp_file)

    def _generate_coq_code(self, spec_dict: Dict[str, Any]) -> str:
        """生成Coq代码"""
        coq_code = """
(* SystemOSIOT Specification Verification *)
Require Import Coq.Lists.List.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Classical.

Module SystemSpecification.
"""

        # 生成系统定义
        for system in spec_dict.get("systems", []):
            coq_code += self._generate_system_coq(system)

        # 生成公理
        for axiom in spec_dict.get("axioms", []):
            coq_code += self._generate_axiom_coq(axiom)

        # 生成定理
        for theorem in spec_dict.get("theorems", []):
            coq_code += self._generate_theorem_coq(theorem)

        coq_code += "\nEnd SystemSpecification.\n"
        return coq_code

    def _generate_system_coq(self, system: Dict[str, Any]) -> str:
        """生成系统Coq代码"""
        name = system.get("name", "System")
        elements = system.get("elements", [])

        coq_code = f"""
(* System: {name} *)
Inductive {name}_Element : Type :=
"""

        for element in elements:
            coq_code += f"  | {element} : {name}_Element\n"

        coq_code += ".\n\n"
        return coq_code

    def _generate_axiom_coq(self, axiom: Dict[str, Any]) -> str:
        """生成公理Coq代码"""
        name = axiom.get("name", "axiom")
        formula = axiom.get("formula", {})

        coq_code = f"Axiom {name} : "
        coq_code += self._formula_to_coq(formula)
        coq_code += ".\n\n"

        return coq_code

    def _generate_theorem_coq(self, theorem: Dict[str, Any]) -> str:
        """生成定理Coq代码"""
        name = theorem.get("name", "theorem")
        formula = theorem.get("formula", {})
        proof = theorem.get("proof", [])

        coq_code = f"Theorem {name} : "
        coq_code += self._formula_to_coq(formula)
        coq_code += ".\n"

        # 生成证明
        for step in proof:
            coq_code += self._proof_step_to_coq(step)

        coq_code += "Qed.\n\n"
        return coq_code

    def _formula_to_coq(self, formula: Dict[str, Any]) -> str:
        """将公式转换为Coq格式"""
        formula_type = formula.get("type", "atomic")

        if formula_type == "atomic":
            predicate = formula.get("predicate", "P")
            return f"{predicate}"

        elif formula_type == "binary":
            operator = formula.get("operator", "and")
            left = self._formula_to_coq(formula.get("left", {}))
            right = self._formula_to_coq(formula.get("right", {}))

            if operator == "and":
                return f"({left} /\\ {right})"
            elif operator == "or":
                return f"({left} \\/ {right})"
            elif operator == "implies":
                return f"({left} -> {right})"
            else:
                return f"({left} {operator} {right})"

        elif formula_type == "quantifier":
            quantifier = formula.get("quantifier", "forall")
            variable = formula.get("variable", "x")
            body = self._formula_to_coq(formula.get("body", {}))

            if quantifier == "forall":
                return f"(forall {variable}, {body})"
            elif quantifier == "exists":
                return f"(exists {variable}, {body})"
            else:
                return f"({quantifier} {variable}, {body})"

        else:
            return "True"

    def _proof_step_to_coq(self, step: Dict[str, Any]) -> str:
        """将证明步骤转换为Coq格式"""
        rule = step.get("rule", "auto")
        return f"  {rule}.\n"
```

### 2. 与自动证明工具集成

```python
# tools/specification-checker/integrations/auto_proof_integration.py

from typing import Dict, Any, List
import json
import requests

class AutoProofIntegration:
    """自动证明工具集成"""

    def __init__(self, api_endpoint: str = "http://localhost:8000"):
        self.api_endpoint = api_endpoint

    def prove_theorem(self, theorem: Dict[str, Any],
                     axioms: List[Dict[str, Any]]) -> Dict[str, Any]:
        """证明定理"""
        # 构建证明请求
        proof_request = {
            "theorem": theorem,
            "axioms": axioms,
            "strategy": "auto",
            "timeout": 30
        }

        try:
            # 发送证明请求
            response = requests.post(
                f"{self.api_endpoint}/prove",
                json=proof_request,
                timeout=35
            )

            if response.status_code == 200:
                return response.json()
            else:
                return {
                    "success": False,
                    "error": f"HTTP {response.status_code}: {response.text}"
                }

        except requests.exceptions.RequestException as e:
            return {
                "success": False,
                "error": f"请求失败: {str(e)}"
            }

    def verify_proof(self, proof: List[Dict[str, Any]]) -> Dict[str, Any]:
        """验证证明"""
        verification_request = {
            "proof": proof,
            "verification_level": "strict"
        }

        try:
            response = requests.post(
                f"{self.api_endpoint}/verify",
                json=verification_request,
                timeout=30
            )

            if response.status_code == 200:
                return response.json()
            else:
                return {
                    "success": False,
                    "error": f"HTTP {response.status_code}: {response.text}"
                }

        except requests.exceptions.RequestException as e:
            return {
                "success": False,
                "error": f"请求失败: {str(e)}"
            }
```

### 3. 与IDE集成

```python
# tools/specification-checker/integrations/ide_integration.py

from typing import Dict, Any, List
import json
import os

class IDEIntegration:
    """IDE集成接口"""

    def __init__(self):
        self.language_server = None

    def provide_diagnostics(self, document_uri: str,
                          document_content: str) -> List[Dict[str, Any]]:
        """提供诊断信息"""
        from ..core.checker import SpecificationChecker

        checker = SpecificationChecker()

        # 创建临时文件
        temp_file = f"/tmp/temp_spec_{hash(document_uri)}.spec"
        with open(temp_file, 'w') as f:
            f.write(document_content)

        try:
            # 执行检查
            result = checker.check_specification(temp_file)

            # 转换为LSP诊断格式
            diagnostics = []

            for error in result.errors:
                diagnostics.append({
                    "range": {"start": {"line": 0, "character": 0},
                             "end": {"line": 0, "character": 0}},
                    "message": error,
                    "severity": 1  # Error
                })

            for warning in result.warnings:
                diagnostics.append({
                    "range": {"start": {"line": 0, "character": 0},
                             "end": {"line": 0, "character": 0}},
                    "message": warning,
                    "severity": 2  # Warning
                })

            return diagnostics

        finally:
            # 清理临时文件
            if os.path.exists(temp_file):
                os.unlink(temp_file)

    def provide_completion(self, document_uri: str,
                          position: Dict[str, int]) -> List[Dict[str, Any]]:
        """提供自动补全"""
        completions = [
            {
                "label": "system",
                "kind": 14,  # Keyword
                "detail": "系统定义",
                "documentation": "定义一个新的系统"
            },
            {
                "label": "element",
                "kind": 14,  # Keyword
                "detail": "元素定义",
                "documentation": "定义系统元素"
            },
            {
                "label": "relation",
                "kind": 14,  # Keyword
                "detail": "关系定义",
                "documentation": "定义元素间关系"
            },
            {
                "label": "axiom",
                "kind": 14,  # Keyword
                "detail": "公理定义",
                "documentation": "定义公理"
            },
            {
                "label": "theorem",
                "kind": 14,  # Keyword
                "detail": "定理定义",
                "documentation": "定义定理"
            }
        ]

        return completions

    def provide_hover(self, document_uri: str,
                     position: Dict[str, int]) -> Dict[str, Any]:
        """提供悬停信息"""
        return {
            "contents": [
                {
                    "language": "system-theory",
                    "value": "SystemOSIOT 系统理论规范语言"
                },
                "SystemOSIOT是一个形式化的系统理论规范语言，用于描述和分析复杂系统。"
            ]
        }
```

## 🔧 配置管理

### 配置文件格式

```json
{
  "toolchain": {
    "version": "1.0.0",
    "tools": {
      "coq": {
        "enabled": true,
        "path": "/usr/bin/coqc",
        "timeout": 30
      },
      "auto_proof": {
        "enabled": true,
        "endpoint": "http://localhost:8000",
        "timeout": 30
      },
      "ide": {
        "enabled": true,
        "diagnostics": true,
        "completion": true,
        "hover": true
      }
    },
    "checking": {
      "consistency": true,
      "completeness": true,
      "independence": true,
      "syntax": true,
      "semantics": true
    },
    "reporting": {
      "format": ["json", "html"],
      "output_dir": "./reports",
      "include_details": true
    }
  }
}
```

### 配置加载器

```python
# tools/specification-checker/config/config_loader.py

import json
from pathlib import Path
from typing import Dict, Any

class ConfigLoader:
    """配置加载器"""

    def __init__(self, config_path: str = "toolchain_config.json"):
        self.config_path = Path(config_path)
        self.config = self._load_config()

    def _load_config(self) -> Dict[str, Any]:
        """加载配置"""
        if not self.config_path.exists():
            return self._get_default_config()

        with open(self.config_path, 'r', encoding='utf-8') as f:
            return json.load(f)

    def _get_default_config(self) -> Dict[str, Any]:
        """获取默认配置"""
        return {
            "toolchain": {
                "version": "1.0.0",
                "tools": {
                    "coq": {"enabled": False},
                    "auto_proof": {"enabled": False},
                    "ide": {"enabled": True}
                },
                "checking": {
                    "consistency": True,
                    "completeness": True,
                    "independence": True,
                    "syntax": True,
                    "semantics": True
                },
                "reporting": {
                    "format": ["json"],
                    "output_dir": "./reports",
                    "include_details": True
                }
            }
        }

    def get_tool_config(self, tool_name: str) -> Dict[str, Any]:
        """获取工具配置"""
        return self.config.get("toolchain", {}).get("tools", {}).get(tool_name, {})

    def is_tool_enabled(self, tool_name: str) -> bool:
        """检查工具是否启用"""
        return self.get_tool_config(tool_name).get("enabled", False)

    def get_checking_config(self) -> Dict[str, Any]:
        """获取检查配置"""
        return self.config.get("toolchain", {}).get("checking", {})

    def get_reporting_config(self) -> Dict[str, Any]:
        """获取报告配置"""
        return self.config.get("toolchain", {}).get("reporting", {})
```

## 🚀 使用示例

### 完整工具链使用

```python
# examples/toolchain_usage.py

from tools.specification_checker.core.checker import SpecificationChecker
from tools.specification_checker.integrations.coq_integration import CoqIntegration
from tools.specification_checker.integrations.auto_proof_integration import AutoProofIntegration
from tools.specification_checker.config.config_loader import ConfigLoader

def main():
    """完整工具链使用示例"""

    # 加载配置
    config = ConfigLoader()

    # 创建检查器
    checker = SpecificationChecker()

    # 检查规范
    spec_file = "example.spec"
    result = checker.check_specification(spec_file)

    print("=== 规范检查结果 ===")
    print(f"检查成功: {'是' if result.success else '否'}")

    # 如果检查通过，进行进一步验证
    if result.success and config.is_tool_enabled("coq"):
        print("\n=== Coq验证 ===")
        coq_integration = CoqIntegration()
        coq_result = coq_integration.verify_specification(
            checker._parse_to_dict(result.ast)
        )
        print(f"Coq验证: {'成功' if coq_result['success'] else '失败'}")

    if result.success and config.is_tool_enabled("auto_proof"):
        print("\n=== 自动证明 ===")
        auto_proof = AutoProofIntegration()

        # 对每个定理进行自动证明
        for theorem in result.theorems:
            proof_result = auto_proof.prove_theorem(theorem, result.axioms)
            print(f"定理 {theorem['name']}: {'可证明' if proof_result['success'] else '不可证明'}")

    # 生成报告
    reporting_config = config.get_reporting_config()
    output_dir = reporting_config.get("output_dir", "./reports")

    checker.generate_report(result, f"{output_dir}/check_report")

if __name__ == "__main__":
    main()
```

### IDE插件示例

```python
# examples/ide_plugin.py

import json
from tools.specification_checker.integrations.ide_integration import IDEIntegration

class SystemTheoryLanguageServer:
    """系统理论语言服务器"""

    def __init__(self):
        self.ide_integration = IDEIntegration()

    def handle_request(self, method: str, params: Dict[str, Any]) -> Dict[str, Any]:
        """处理LSP请求"""
        if method == "textDocument/diagnostic":
            return self._handle_diagnostic(params)
        elif method == "textDocument/completion":
            return self._handle_completion(params)
        elif method == "textDocument/hover":
            return self._handle_hover(params)
        else:
            return {"error": f"未知方法: {method}"}

    def _handle_diagnostic(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """处理诊断请求"""
        document_uri = params["textDocument"]["uri"]
        document_content = params["textDocument"]["content"]

        diagnostics = self.ide_integration.provide_diagnostics(
            document_uri, document_content
        )

        return {
            "jsonrpc": "2.0",
            "id": params.get("id"),
            "result": {
                "diagnostics": diagnostics
            }
        }

    def _handle_completion(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """处理补全请求"""
        document_uri = params["textDocument"]["uri"]
        position = params["position"]

        completions = self.ide_integration.provide_completion(
            document_uri, position
        )

        return {
            "jsonrpc": "2.0",
            "id": params.get("id"),
            "result": {
                "isIncomplete": False,
                "items": completions
            }
        }

    def _handle_hover(self, params: Dict[str, Any]) -> Dict[str, Any]:
        """处理悬停请求"""
        document_uri = params["textDocument"]["uri"]
        position = params["position"]

        hover_info = self.ide_integration.provide_hover(
            document_uri, position
        )

        return {
            "jsonrpc": "2.0",
            "id": params.get("id"),
            "result": hover_info
        }

# 启动语言服务器
if __name__ == "__main__":
    server = SystemTheoryLanguageServer()

    # 模拟LSP请求
    diagnostic_request = {
        "jsonrpc": "2.0",
        "id": 1,
        "method": "textDocument/diagnostic",
        "params": {
            "textDocument": {
                "uri": "file:///example.spec",
                "content": "system TestSystem { element: a, b; }"
            }
        }
    }

    response = server.handle_request(
        diagnostic_request["method"],
        diagnostic_request["params"]
    )

    print("LSP响应:", json.dumps(response, indent=2))
```

## 📋 部署指南

### 1. 环境要求

- Python 3.8+
- Coq 8.15+ (可选)
- 自动证明工具 (可选)

### 2. 安装步骤

```bash
# 1. 克隆项目
git clone https://github.com/systemosiot/specification-checker.git
cd specification-checker

# 2. 安装依赖
pip install -r requirements.txt

# 3. 配置工具链
cp toolchain_config.example.json toolchain_config.json
# 编辑配置文件

# 4. 测试安装
python -m tools.specification_checker.core.checker
```

### 3. IDE集成

#### VS Code扩展

```json
// package.json
{
  "name": "systemosiot-spec",
  "displayName": "SystemOSIOT Specification",
  "description": "SystemOSIOT规范语言支持",
  "version": "1.0.0",
  "engines": {
    "vscode": "^1.60.0"
  },
  "categories": ["Programming Languages"],
  "activationEvents": ["onLanguage:systemosiot"],
  "main": "./out/extension.js",
  "contributes": {
    "languages": [{
      "id": "systemosiot",
      "aliases": ["SystemOSIOT", "systemosiot"],
      "extensions": [".spec"],
      "configuration": "./language-configuration.json"
    }],
    "grammars": [{
      "language": "systemosiot",
      "scopeName": "source.systemosiot",
      "path": "./syntaxes/systemosiot.tmLanguage.json"
    }]
  }
}
```

## 🔍 故障排除

### 常见问题

1. **Coq验证失败**
   - 检查Coq是否正确安装
   - 验证Coq版本兼容性
   - 检查生成的Coq代码语法

2. **自动证明工具连接失败**
   - 确认服务端点正确
   - 检查网络连接
   - 验证API格式

3. **IDE集成问题**
   - 检查LSP协议版本
   - 验证文件路径格式
   - 确认语言服务器配置

### 调试模式

```python
import logging

# 启用调试日志
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
)

# 运行检查器
checker = SpecificationChecker()
result = checker.check_specification("debug.spec")
```

## 📚 扩展开发

### 添加新工具集成

1. 创建集成模块
2. 实现标准接口
3. 更新配置管理
4. 添加测试用例

### 自定义检查规则

1. 继承基础检查器
2. 实现自定义逻辑
3. 注册到工具链
4. 配置启用条件

---

**版本**: 1.0.0
**最后更新**: 2024年12月
**维护者**: SystemOSIOT开发团队
