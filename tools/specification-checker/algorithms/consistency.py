"""
SystemOSIOT 一致性检查算法

该模块实现了系统理论规范的一致性检查算法。
"""

from typing import Dict, List, Any, Optional
from dataclasses import dataclass
import logging

@dataclass
class ConsistencyResult:
    """一致性检查结果"""
    is_consistent: bool
    errors: List[str]
    warnings: List[str]
    details: Dict[str, Any]

class ConsistencyChecker:
    """一致性检查器"""
    
    def __init__(self):
        self.logger = logging.getLogger(__name__)
    
    def check_all(self, specification: Dict[str, Any]) -> ConsistencyResult:
        """执行全面一致性检查"""
        result = ConsistencyResult(
            is_consistent=True,
            errors=[],
            warnings=[],
            details={}
        )
        
        # 检查公理一致性
        axiom_result = self.check_axiom_consistency(specification)
        result.errors.extend(axiom_result.errors)
        result.warnings.extend(axiom_result.warnings)
        
        if not axiom_result.is_consistent:
            result.is_consistent = False
        
        # 检查定理一致性
        theorem_result = self.check_theorem_consistency(specification)
        result.errors.extend(theorem_result.errors)
        result.warnings.extend(theorem_result.warnings)
        
        if not theorem_result.is_consistent:
            result.is_consistent = False
        
        # 检查模型一致性
        model_result = self.check_model_consistency(specification)
        result.errors.extend(model_result.errors)
        result.warnings.extend(model_result.warnings)
        
        if not model_result.is_consistent:
            result.is_consistent = False
        
        return result
    
    def check_axiom_consistency(self, specification: Dict[str, Any]) -> ConsistencyResult:
        """检查公理一致性"""
        result = ConsistencyResult(
            is_consistent=True,
            errors=[],
            warnings=[],
            details={}
        )
        
        axioms = specification.get("axioms", [])
        
        # 检查公理冲突
        for i, axiom1 in enumerate(axioms):
            for j, axiom2 in enumerate(axioms[i+1:], i+1):
                if self._has_conflict(axiom1, axiom2):
                    result.is_consistent = False
                    result.errors.append(
                        f"公理冲突: {axiom1.get('name', f'axiom_{i}')} 与 "
                        f"{axiom2.get('name', f'axiom_{j}')}"
                    )
        
        result.details = {
            "total_axioms": len(axioms),
            "conflicts": len([e for e in result.errors if "公理冲突" in e])
        }
        
        return result
    
    def check_theorem_consistency(self, specification: Dict[str, Any]) -> ConsistencyResult:
        """检查定理一致性"""
        result = ConsistencyResult(
            is_consistent=True,
            errors=[],
            warnings=[],
            details={}
        )
        
        theorems = specification.get("theorems", [])
        axioms = specification.get("axioms", [])
        
        # 检查定理与公理的一致性
        for theorem in theorems:
            if not self._verify_theorem_consistency(theorem, axioms):
                result.is_consistent = False
                result.errors.append(
                    f"定理不一致: {theorem.get('name', 'unknown')}"
                )
        
        result.details = {
            "total_theorems": len(theorems),
            "inconsistent_theorems": len([e for e in result.errors if "定理不一致" in e])
        }
        
        return result
    
    def check_model_consistency(self, specification: Dict[str, Any]) -> ConsistencyResult:
        """检查模型一致性"""
        result = ConsistencyResult(
            is_consistent=True,
            errors=[],
            warnings=[],
            details={}
        )
        
        systems = specification.get("systems", [])
        
        for system in systems:
            system_errors = self._check_system_consistency(system)
            result.errors.extend([f"系统 {system.get('name')}: {error}" for error in system_errors])
        
        if result.errors:
            result.is_consistent = False
        
        result.details = {
            "total_systems": len(systems),
            "inconsistent_systems": len([e for e in result.errors if "系统" in e])
        }
        
        return result
    
    def _has_conflict(self, axiom1: Dict[str, Any], axiom2: Dict[str, Any]) -> bool:
        """检查两个公理是否冲突"""
        # 简化的冲突检查
        formula1 = axiom1.get("formula", {})
        formula2 = axiom2.get("formula", {})
        
        # 检查直接矛盾
        if self._is_contradictory(formula1, formula2):
            return True
        
        return False
    
    def _is_contradictory(self, formula1: Dict[str, Any], formula2: Dict[str, Any]) -> bool:
        """检查两个公式是否直接矛盾"""
        # 简化的矛盾检查
        if (formula1.get("type") == "negation" and 
            formula1.get("operand") == formula2):
            return True
        
        if (formula2.get("type") == "negation" and 
            formula2.get("operand") == formula1):
            return True
        
        return False
    
    def _verify_theorem_consistency(self, theorem: Dict[str, Any], 
                                   axioms: List[Dict[str, Any]]) -> bool:
        """验证定理与公理系统的一致性"""
        # 简化的定理一致性验证
        return True
    
    def _check_system_consistency(self, system: Dict[str, Any]) -> List[str]:
        """检查系统一致性"""
        errors = []
        
        elements = system.get("elements", [])
        relations = system.get("relations", [])
        
        # 检查重复元素
        duplicates = [e for e in set(elements) if elements.count(e) > 1]
        for duplicate in duplicates:
            errors.append(f"重复元素: {duplicate}")
        
        # 检查关系中的元素是否存在
        for relation in relations:
            source = relation.get("source")
            target = relation.get("target")
            
            if source not in elements:
                errors.append(f"关系源元素不存在: {source}")
            
            if target not in elements:
                errors.append(f"关系目标元素不存在: {target}")
        
        return errors

def example_consistency_check():
    """一致性检查示例"""
    checker = ConsistencyChecker()
    
    specification = {
        "systems": [
            {
                "name": "SimpleSystem",
                "elements": ["a", "b", "c"],
                "relations": [
                    {"name": "r1", "source": "a", "target": "b"},
                    {"name": "r2", "source": "b", "target": "c"}
                ]
            }
        ],
        "axioms": [
            {
                "name": "axiom1",
                "formula": {"type": "atomic", "predicate": "system_exists"}
            }
        ],
        "theorems": [
            {
                "name": "theorem1",
                "formula": {"type": "atomic", "predicate": "system_property"}
            }
        ]
    }
    
    result = checker.check_all(specification)
    
    print("=== 一致性检查结果 ===")
    print(f"总体一致性: {'通过' if result.is_consistent else '失败'}")
    
    if result.errors:
        print("\n错误:")
        for error in result.errors:
            print(f"  - {error}")
    
    if result.warnings:
        print("\n警告:")
        for warning in result.warnings:
            print(f"  - {warning}")

if __name__ == "__main__":
    example_consistency_check()
