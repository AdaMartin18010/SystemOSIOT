#!/usr/bin/env python3
"""
2025年最新知识图谱构建工具
基于系统理论的概念关系自动提取和可视化
"""

import json
import networkx as nx
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm
from typing import Dict, List, Set, Tuple, Any
from dataclasses import dataclass
from enum import Enum
import re
import os

class RelationType(Enum):
    IS_A = "is_a"
    PART_OF = "part_of"
    CAUSES = "causes"
    IMPLIES = "implies"
    EQUIVALENT = "equivalent"
    OPPOSITE = "opposite"
    DEPENDS_ON = "depends_on"
    USES = "uses"
    INSTANCE_OF = "instance_of"

@dataclass
class Concept:
    name: str
    definition: str
    properties: List[str]
    examples: List[str]

@dataclass
class Relation:
    source: str
    target: str
    relation_type: RelationType
    confidence: float
    evidence: List[str]

class KnowledgeGraphBuilder:
    """
    2025年最新知识图谱构建器
    支持系统理论概念关系自动提取和可视化
    """
    
    def __init__(self):
        self.concepts: Dict[str, Concept] = {}
        self.relations: List[Relation] = []
        self.graph = nx.DiGraph()
        
        # 关系模式
        self.relation_patterns = {
            RelationType.IS_A: [
                r"(.+?)\s+是\s+(.+?)(?:的|$)",
                r"(.+?)\s+属于\s+(.+?)(?:的|$)",
                r"(.+?)\s+为\s+(.+?)(?:的|$)"
            ],
            RelationType.PART_OF: [
                r"(.+?)\s+包含\s+(.+?)(?:的|$)",
                r"(.+?)\s+由\s+(.+?)(?:组成|构成|$)",
                r"(.+?)\s+包括\s+(.+?)(?:的|$)"
            ],
            RelationType.CAUSES: [
                r"(.+?)\s+导致\s+(.+?)(?:的|$)",
                r"(.+?)\s+引起\s+(.+?)(?:的|$)",
                r"(.+?)\s+产生\s+(.+?)(?:的|$)"
            ],
            RelationType.IMPLIES: [
                r"(.+?)\s+意味着\s+(.+?)(?:的|$)",
                r"(.+?)\s+表明\s+(.+?)(?:的|$)",
                r"(.+?)\s+说明\s+(.+?)(?:的|$)"
            ],
            RelationType.EQUIVALENT: [
                r"(.+?)\s+等价于\s+(.+?)(?:的|$)",
                r"(.+?)\s+等于\s+(.+?)(?:的|$)",
                r"(.+?)\s+等同于\s+(.+?)(?:的|$)"
            ],
            RelationType.OPPOSITE: [
                r"(.+?)\s+与\s+(.+?)\s+相反",
                r"(.+?)\s+对立于\s+(.+?)(?:的|$)",
                r"(.+?)\s+与\s+(.+?)\s+矛盾"
            ],
            RelationType.DEPENDS_ON: [
                r"(.+?)\s+依赖于\s+(.+?)(?:的|$)",
                r"(.+?)\s+基于\s+(.+?)(?:的|$)",
                r"(.+?)\s+需要\s+(.+?)(?:的|$)"
            ],
            RelationType.USES: [
                r"(.+?)\s+使用\s+(.+?)(?:的|$)",
                r"(.+?)\s+利用\s+(.+?)(?:的|$)",
                r"(.+?)\s+应用\s+(.+?)(?:的|$)"
            ]
        }
    
    def add_concept(self, concept: Concept):
        """添加概念"""
        self.concepts[concept.name] = concept
        self.graph.add_node(concept.name, 
            definition=concept.definition,
            properties=concept.properties,
                          examples=concept.examples)
    
    def add_relation(self, relation: Relation):
        """添加关系"""
        self.relations.append(relation)
        self.graph.add_edge(relation.source, relation.target,
                          relation_type=relation.relation_type.value,
                          confidence=relation.confidence,
                          evidence=relation.evidence)
    
    def extract_concepts_from_text(self, text: str) -> List[Concept]:
        """从文本中提取概念"""
        concepts = []
        
        # 提取定义模式
        definition_patterns = [
            r"**定义\s*(\d+\.\d+)?\s*\((.+?)\)\s*:\s*(.+?)(?:\n|$)",
            r"**(.+?)**\s*:\s*(.+?)(?:\n|$)",
            r"(.+?)\s*是\s*(.+?)(?:的|$)",
            r"(.+?)\s*定义为\s*(.+?)(?:的|$)"
        ]
        
        for pattern in definition_patterns:
            matches = re.finditer(pattern, text, re.MULTILINE | re.IGNORECASE)
            for match in matches:
                if len(match.groups()) >= 2:
                    name = match.group(1).strip()
                    definition = match.group(2).strip()
                    
                    # 提取属性
                    properties = self._extract_properties(text, name)
                    
                    # 提取示例
                    examples = self._extract_examples(text, name)
                    
                concept = Concept(
                        name=name,
                        definition=definition,
                        properties=properties,
                        examples=examples
                )
                concepts.append(concept)
        
        return concepts
    
    def extract_relations_from_text(self, text: str) -> List[Relation]:
        """从文本中提取关系"""
        relations = []
        
        for relation_type, patterns in self.relation_patterns.items():
            for pattern in patterns:
                matches = re.finditer(pattern, text, re.MULTILINE | re.IGNORECASE)
                for match in matches:
                    if len(match.groups()) >= 2:
                        source = match.group(1).strip()
                        target = match.group(2).strip()
                        
                        # 计算置信度
                        confidence = self._calculate_confidence(match.group(0), relation_type)
                        
                        # 提取证据
                        evidence = [match.group(0)]
                        
                        relation = Relation(
                            source=source,
                            target=target,
                            relation_type=relation_type,
                            confidence=confidence,
                            evidence=evidence
                        )
                        relations.append(relation)
        
        return relations
    
    def _extract_properties(self, text: str, concept_name: str) -> List[str]:
        """提取概念属性"""
        properties = []
        
        # 查找概念相关的属性描述
        concept_pattern = rf"{re.escape(concept_name)}.*?(?:具有|拥有|包含|包括)(.+?)(?:\n|$)"
        matches = re.finditer(concept_pattern, text, re.MULTILINE | re.IGNORECASE)
        
        for match in matches:
            prop_text = match.group(1).strip()
            # 分割属性
            props = re.split(r'[,，;；]', prop_text)
            properties.extend([p.strip() for p in props if p.strip()])
        
        return properties
    
    def _extract_examples(self, text: str, concept_name: str) -> List[str]:
        """提取概念示例"""
        examples = []
        
        # 查找概念相关的示例
        example_patterns = [
            rf"{re.escape(concept_name)}.*?(?:例如|比如|如|包括)(.+?)(?:\n|$)",
            rf"(?:例如|比如|如)\s*{re.escape(concept_name)}.*?(.+?)(?:\n|$)"
        ]
        
        for pattern in example_patterns:
            matches = re.finditer(pattern, text, re.MULTILINE | re.IGNORECASE)
            for match in matches:
                example_text = match.group(1).strip()
                # 分割示例
                exs = re.split(r'[,，;；]', example_text)
                examples.extend([e.strip() for e in exs if e.strip()])
        
        return examples
    
    def _calculate_confidence(self, text: str, relation_type: RelationType) -> float:
        """计算关系置信度"""
        base_confidence = 0.5
        
        # 根据关键词调整置信度
        confidence_boosters = {
            "明确": 0.2,
            "显然": 0.2,
            "显然": 0.2,
            "必然": 0.3,
            "一定": 0.3,
            "总是": 0.3,
            "所有": 0.2,
            "每个": 0.2
        }
        
        for keyword, boost in confidence_boosters.items():
            if keyword in text:
                base_confidence += boost
        
        return min(base_confidence, 1.0)
    
    def build_graph_from_files(self, file_paths: List[str]):
        """从文件构建知识图谱"""
        for file_path in file_paths:
            if os.path.exists(file_path):
                with open(file_path, 'r', encoding='utf-8') as f:
                    text = f.read()
                
                # 提取概念和关系
                concepts = self.extract_concepts_from_text(text)
                relations = self.extract_relations_from_text(text)
                
                # 添加到图谱
                for concept in concepts:
                    self.add_concept(concept)
                
                for relation in relations:
                    self.add_relation(relation)
    
    def visualize_graph(self, output_path: str = "knowledge_graph.png"):
        """可视化知识图谱"""
        plt.figure(figsize=(20, 16))
        
        # 设置中文字体
        plt.rcParams['font.sans-serif'] = ['SimHei', 'DejaVu Sans']
        plt.rcParams['axes.unicode_minus'] = False
        
        # 计算布局
        pos = nx.spring_layout(self.graph, k=3, iterations=50)
        
        # 绘制节点
        nx.draw_networkx_nodes(self.graph, pos, 
                              node_color='lightblue',
                              node_size=1000,
                              alpha=0.7)
        
        # 绘制边
        edge_colors = []
        for edge in self.graph.edges():
            relation_type = self.graph[edge[0]][edge[1]]['relation_type']
            color_map = {
                'is_a': 'red',
                'part_of': 'blue',
                'causes': 'green',
                'implies': 'orange',
                'equivalent': 'purple',
                'opposite': 'brown',
                'depends_on': 'pink',
                'uses': 'gray'
            }
            edge_colors.append(color_map.get(relation_type, 'black'))
        
        nx.draw_networkx_edges(self.graph, pos,
            edge_color=edge_colors,
            arrows=True,
                              arrowsize=20,
                              alpha=0.6)
        
        # 绘制标签
        labels = {}
        for node in self.graph.nodes():
            labels[node] = node
        
        nx.draw_networkx_labels(self.graph, pos, labels, font_size=8)
        
        # 添加图例
        legend_elements = []
        for relation_type in RelationType:
            color_map = {
                'is_a': 'red',
                'part_of': 'blue',
                'causes': 'green',
                'implies': 'orange',
                'equivalent': 'purple',
                'opposite': 'brown',
                'depends_on': 'pink',
                'uses': 'gray'
            }
            color = color_map.get(relation_type.value, 'black')
            legend_elements.append(plt.Line2D([0], [0], color=color, lw=2, label=relation_type.value))
        
        plt.legend(handles=legend_elements, loc='upper right')
        
        plt.title("系统理论知识图谱", fontsize=16, fontweight='bold')
        plt.axis('off')
        plt.tight_layout()
        plt.savefig(output_path, dpi=300, bbox_inches='tight')
        plt.show()
    
    def export_to_json(self, output_path: str = "knowledge_graph.json"):
        """导出知识图谱到JSON"""
        data = {
            "concepts": {},
            "relations": []
        }
        
        # 导出概念
        for name, concept in self.concepts.items():
            data["concepts"][name] = {
                "definition": concept.definition,
                "properties": concept.properties,
                "examples": concept.examples
            }
        
        # 导出关系
        for relation in self.relations:
            data["relations"].append({
                "source": relation.source,
                "target": relation.target,
                "relation_type": relation.relation_type.value,
                "confidence": relation.confidence,
                "evidence": relation.evidence
            })
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    
    def validate_consistency(self) -> List[str]:
        """验证知识图谱一致性"""
        issues = []
        
        # 检查循环依赖
        try:
            cycles = list(nx.simple_cycles(self.graph))
            if cycles:
                issues.append(f"发现循环依赖: {cycles}")
        except:
            pass
        
        # 检查孤立节点
        isolated_nodes = list(nx.isolates(self.graph))
        if isolated_nodes:
            issues.append(f"发现孤立节点: {isolated_nodes}")
        
        # 检查关系一致性
        for relation in self.relations:
            if relation.source not in self.concepts:
                issues.append(f"关系源概念不存在: {relation.source}")
            if relation.target not in self.concepts:
                issues.append(f"关系目标概念不存在: {relation.target}")
        
        return issues
    
    def get_concept_neighbors(self, concept_name: str, depth: int = 1) -> Dict[str, List[str]]:
        """获取概念邻居"""
        if concept_name not in self.graph:
            return {}
        
        neighbors = {
            "incoming": [],
            "outgoing": []
        }
        
        # 获取入边
        for predecessor in self.graph.predecessors(concept_name):
            edge_data = self.graph[predecessor][concept_name]
            neighbors["incoming"].append({
                "concept": predecessor,
                "relation": edge_data["relation_type"],
                "confidence": edge_data["confidence"]
            })
        
        # 获取出边
        for successor in self.graph.successors(concept_name):
            edge_data = self.graph[concept_name][successor]
            neighbors["outgoing"].append({
                "concept": successor,
                "relation": edge_data["relation_type"],
                "confidence": edge_data["confidence"]
            })
        
        return neighbors
    
    def find_shortest_path(self, source: str, target: str) -> List[str]:
        """查找最短路径"""
        try:
            path = nx.shortest_path(self.graph, source, target)
            return path
        except nx.NetworkXNoPath:
            return []
    
    def get_statistics(self) -> Dict[str, Any]:
        """获取图谱统计信息"""
        return {
            "concept_count": len(self.concepts),
            "relation_count": len(self.relations),
            "node_count": self.graph.number_of_nodes(),
            "edge_count": self.graph.number_of_edges(),
            "density": nx.density(self.graph),
            "average_clustering": nx.average_clustering(self.graph.to_undirected()),
            "relation_type_distribution": self._get_relation_type_distribution()
        }
    
    def _get_relation_type_distribution(self) -> Dict[str, int]:
        """获取关系类型分布"""
        distribution = {}
        for relation in self.relations:
            relation_type = relation.relation_type.value
            distribution[relation_type] = distribution.get(relation_type, 0) + 1
        return distribution

def main():
    """主函数"""
    builder = KnowledgeGraphBuilder()
    
    # 示例：从文件构建知识图谱
    file_paths = [
        "1.系统理论/1.3 形式化结构/1.3.1 数学基础.md",
        "1.系统理论/1.4 形式化证明/1.4.1 命题与定理.md",
        "1.系统理论/1.6 形式语义/1.6.12 完整语义理论体系.md"
    ]
    
    # 构建知识图谱
    builder.build_graph_from_files(file_paths)
    
    # 验证一致性
    issues = builder.validate_consistency()
        if issues:
            print("发现一致性问题:")
            for issue in issues:
            print(f"- {issue}")
        else:
        print("知识图谱一致性验证通过")
    
    # 获取统计信息
    stats = builder.get_statistics()
    print(f"\n知识图谱统计信息:")
    print(f"- 概念数量: {stats['concept_count']}")
    print(f"- 关系数量: {stats['relation_count']}")
    print(f"- 图谱密度: {stats['density']:.3f}")
    
    # 可视化
    builder.visualize_graph()
    
    # 导出
    builder.export_to_json()

if __name__ == "__main__":
    main()