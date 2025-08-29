"""
SystemOSIOT 系统理论规范语言

该模块定义了系统理论的形式化规范语言，包括：
1. 语法定义
2. 语义解释
3. 解析器实现
4. 验证规则
"""

from typing import Dict, List, Optional, Union, Any
from dataclasses import dataclass
from enum import Enum
import re
import json

# ============================================================================
# 语言基础定义
# ============================================================================

class TokenType(Enum):
    """词法单元类型"""
    # 关键字
    SYSTEM = "SYSTEM"
    ELEMENT = "ELEMENT"
    RELATION = "RELATION"
    BOUNDARY = "BOUNDARY"
    FUNCTION = "FUNCTION"
    AXIOM = "AXIOM"
    THEOREM = "THEOREM"
    PROOF = "PROOF"
    
    # 逻辑符号
    FORALL = "FORALL"  # ∀
    EXISTS = "EXISTS"  # ∃
    IMPLIES = "IMPLIES"  # →
    AND = "AND"  # ∧
    OR = "OR"  # ∨
    NOT = "NOT"  # ¬
    EQUALS = "EQUALS"  # =
    IN = "IN"  # ∈
    SUBSET = "SUBSET"  # ⊆
    END = "END"
    BY = "BY"
    FROM = "FROM"
    
    # 标点符号
    LPAREN = "LPAREN"  # (
    RPAREN = "RPAREN"  # )
    LBRACE = "LBRACE"  # {
    RBRACE = "RBRACE"  # }
    COMMA = "COMMA"  # ,
    SEMICOLON = "SEMICOLON"  # ;
    COLON = "COLON"  # :
    
    # 标识符和字面量
    IDENTIFIER = "IDENTIFIER"
    NUMBER = "NUMBER"
    STRING = "STRING"
    
    # 特殊符号
    EOF = "EOF"
    ERROR = "ERROR"


@dataclass
class Token:
    """词法单元"""
    type: TokenType
    value: str
    line: int
    column: int


@dataclass
class ASTNode:
    """抽象语法树节点"""
    node_type: str
    value: Any
    children: List['ASTNode']
    line: int
    column: int


# ============================================================================
# 语法定义
# ============================================================================

class SystemTheoryGrammar:
    """系统理论语法定义"""
    
    def __init__(self):
        self.rules = {
            # 系统定义
            "system_def": [
                "SYSTEM IDENTIFIER LBRACE system_body RBRACE"
            ],
            
            # 系统体
            "system_body": [
                "element_def relation_def boundary_def function_def",
                "element_def relation_def boundary_def",
                "element_def relation_def",
                "element_def"
            ],
            
            # 元素定义
            "element_def": [
                "ELEMENT COLON element_list SEMICOLON"
            ],
            
            # 元素列表
            "element_list": [
                "IDENTIFIER",
                "element_list COMMA IDENTIFIER"
            ],
            
            # 关系定义
            "relation_def": [
                "RELATION COLON relation_list SEMICOLON"
            ],
            
            # 关系列表
            "relation_list": [
                "relation_item",
                "relation_list COMMA relation_item"
            ],
            
            # 关系项
            "relation_item": [
                "IDENTIFIER LPAREN IDENTIFIER COMMA IDENTIFIER RPAREN"
            ],
            
            # 边界定义
            "boundary_def": [
                "BOUNDARY COLON boundary_condition SEMICOLON"
            ],
            
            # 边界条件
            "boundary_condition": [
                "IDENTIFIER IN IDENTIFIER",
                "IDENTIFIER SUBSET IDENTIFIER"
            ],
            
            # 函数定义
            "function_def": [
                "FUNCTION COLON function_list SEMICOLON"
            ],
            
            # 函数列表
            "function_list": [
                "IDENTIFIER",
                "function_list COMMA IDENTIFIER"
            ],
            
            # 公理定义
            "axiom_def": [
                "AXIOM IDENTIFIER COLON logical_formula SEMICOLON"
            ],
            
            # 定理定义
            "theorem_def": [
                "THEOREM IDENTIFIER COLON logical_formula PROOF proof_body END"
            ],
            
            # 逻辑公式
            "logical_formula": [
                "atomic_formula",
                "NOT logical_formula",
                "logical_formula AND logical_formula",
                "logical_formula OR logical_formula",
                "logical_formula IMPLIES logical_formula",
                "FORALL IDENTIFIER COLON logical_formula",
                "EXISTS IDENTIFIER COLON logical_formula",
                "LPAREN logical_formula RPAREN"
            ],
            
            # 原子公式
            "atomic_formula": [
                "IDENTIFIER LPAREN term_list RPAREN",
                "term EQUALS term",
                "term IN term",
                "term SUBSET term"
            ],
            
            # 项列表
            "term_list": [
                "term",
                "term_list COMMA term"
            ],
            
            # 项
            "term": [
                "IDENTIFIER",
                "NUMBER",
                "STRING"
            ],
            
            # 证明体
            "proof_body": [
                "proof_step",
                "proof_body proof_step"
            ],
            
            # 证明步骤
            "proof_step": [
                "IDENTIFIER COLON proof_rule SEMICOLON"
            ],
            
            # 证明规则
            "proof_rule": [
                "logical_formula",
                "logical_formula BY IDENTIFIER",
                "logical_formula FROM term_list"
            ]
        }


# ============================================================================
# 词法分析器
# ============================================================================

class Lexer:
    """词法分析器"""
    
    def __init__(self, text: str):
        self.text = text
        self.pos = 0
        self.line = 1
        self.column = 1
        self.tokens = []
        
        # 关键字映射
        self.keywords = {
            'system': TokenType.SYSTEM,
            'element': TokenType.ELEMENT,
            'relation': TokenType.RELATION,
            'boundary': TokenType.BOUNDARY,
            'function': TokenType.FUNCTION,
            'axiom': TokenType.AXIOM,
            'theorem': TokenType.THEOREM,
            'proof': TokenType.PROOF,
            'forall': TokenType.FORALL,
            'exists': TokenType.EXISTS,
            'and': TokenType.AND,
            'or': TokenType.OR,
            'not': TokenType.NOT,
            'in': TokenType.IN,
            'subset': TokenType.SUBSET,
            'end': TokenType.END,
            'by': TokenType.BY,
            'from': TokenType.FROM
        }
        
        # 符号映射
        self.symbols = {
            '→': TokenType.IMPLIES,
            '∧': TokenType.AND,
            '∨': TokenType.OR,
            '¬': TokenType.NOT,
            '=': TokenType.EQUALS,
            '∈': TokenType.IN,
            '⊆': TokenType.SUBSET,
            '(': TokenType.LPAREN,
            ')': TokenType.RPAREN,
            '{': TokenType.LBRACE,
            '}': TokenType.RBRACE,
            ',': TokenType.COMMA,
            ';': TokenType.SEMICOLON,
            ':': TokenType.COLON
        }
    
    def tokenize(self) -> List[Token]:
        """词法分析主函数"""
        while self.pos < len(self.text):
            char = self.text[self.pos]
            
            # 跳过空白字符
            if char.isspace():
                self._skip_whitespace()
                continue
            
            # 跳过注释
            if char == '/' and self._peek() == '/':
                self._skip_comment()
                continue
            
            # 处理标识符和关键字
            if char.isalpha() or char == '_':
                token = self._read_identifier()
                self.tokens.append(token)
                continue
            
            # 处理数字
            if char.isdigit():
                token = self._read_number()
                self.tokens.append(token)
                continue
            
            # 处理字符串
            if char == '"':
                token = self._read_string()
                self.tokens.append(token)
                continue
            
            # 处理符号
            if char in self.symbols:
                token = Token(
                    type=self.symbols[char],
                    value=char,
                    line=self.line,
                    column=self.column
                )
                self.tokens.append(token)
                self._advance()
                continue
            
            # 未知字符
            token = Token(
                type=TokenType.ERROR,
                value=char,
                line=self.line,
                column=self.column
            )
            self.tokens.append(token)
            self._advance()
        
        # 添加EOF标记
        self.tokens.append(Token(
            type=TokenType.EOF,
            value="",
            line=self.line,
            column=self.column
        ))
        
        return self.tokens
    
    def _skip_whitespace(self):
        """跳过空白字符"""
        while self.pos < len(self.text) and self.text[self.pos].isspace():
            if self.text[self.pos] == '\n':
                self.line += 1
                self.column = 1
            else:
                self.column += 1
            self.pos += 1
    
    def _skip_comment(self):
        """跳过注释"""
        while self.pos < len(self.text) and self.text[self.pos] != '\n':
            self.pos += 1
            self.column += 1
    
    def _read_identifier(self) -> Token:
        """读取标识符或关键字"""
        start_pos = self.pos
        start_column = self.column
        
        while (self.pos < len(self.text) and 
               (self.text[self.pos].isalnum() or self.text[self.pos] == '_')):
            self.pos += 1
            self.column += 1
        
        value = self.text[start_pos:self.pos]
        
        # 检查是否为关键字
        if value.lower() in self.keywords:
            return Token(
                type=self.keywords[value.lower()],
                value=value,
                line=self.line,
                column=start_column
            )
        
        return Token(
            type=TokenType.IDENTIFIER,
            value=value,
            line=self.line,
            column=start_column
        )
    
    def _read_number(self) -> Token:
        """读取数字"""
        start_pos = self.pos
        start_column = self.column
        
        while (self.pos < len(self.text) and 
               (self.text[self.pos].isdigit() or self.text[self.pos] == '.')):
            self.pos += 1
            self.column += 1
        
        value = self.text[start_pos:self.pos]
        
        return Token(
            type=TokenType.NUMBER,
            value=value,
            line=self.line,
            column=start_column
        )
    
    def _read_string(self) -> Token:
        """读取字符串"""
        start_column = self.column
        self.pos += 1  # 跳过开始的引号
        self.column += 1
        
        value = ""
        while (self.pos < len(self.text) and 
               self.text[self.pos] != '"'):
            if self.text[self.pos] == '\\':
                self.pos += 1
                self.column += 1
                if self.pos < len(self.text):
                    value += self.text[self.pos]
            else:
                value += self.text[self.pos]
            self.pos += 1
            self.column += 1
        
        if self.pos < len(self.text):
            self.pos += 1  # 跳过结束的引号
            self.column += 1
        
        return Token(
            type=TokenType.STRING,
            value=value,
            line=self.line,
            column=start_column
        )
    
    def _peek(self) -> Optional[str]:
        """查看下一个字符"""
        if self.pos + 1 < len(self.text):
            return self.text[self.pos + 1]
        return None
    
    def _advance(self):
        """前进一个字符"""
        self.pos += 1
        self.column += 1


# ============================================================================
# 语法分析器（占位符）
# ============================================================================

class Parser:
    """语法分析器（占位符实现）"""
    
    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.pos = 0
    
    def parse(self) -> ASTNode:
        """解析主函数（占位符）"""
        # 这里应该实现完整的语法分析逻辑
        # 目前返回一个简单的占位符节点
        return ASTNode(
            node_type="root",
            value="parsed",
            children=[],
            line=1,
            column=1
        )


# ============================================================================
# 规范语言类
# ============================================================================

class SystemTheoryLanguage:
    """系统理论规范语言"""
    
    def __init__(self):
        self.lexer = None
        self.parser = None
    
    def parse(self, text: str) -> ASTNode:
        """解析规范文本"""
        # 词法分析
        self.lexer = Lexer(text)
        tokens = self.lexer.tokenize()
        
        # 语法分析
        self.parser = Parser(tokens)
        ast = self.parser.parse()
        
        return ast
    
    def check_syntax(self, text: str) -> Dict[str, Any]:
        """检查语法"""
        try:
            ast = self.parse(text)
            return {
                "valid": True,
                "ast": ast,
                "errors": []
            }
        except SyntaxError as e:
            return {
                "valid": False,
                "ast": None,
                "errors": [str(e)]
            }


# ============================================================================
# 示例和测试
# ============================================================================

def example_system_specification():
    """示例系统规范"""
    return """
    system SimpleSystem {
        element: a, b, c;
        relation: r1(a, b), r2(b, c);
        boundary: a in SimpleSystem;
        function: f1, f2;
    }
    
    axiom axiom1: forall x: element(x) implies exists y: relation(x, y);
    axiom axiom2: forall x: element(x) implies x in SimpleSystem;
    
    theorem theorem1: forall x: element(x) implies function(f1);
    proof
        step1: element(x) by axiom1;
        step2: function(f1) from step1;
    end
    """


def test_language():
    """测试语言功能"""
    language = SystemTheoryLanguage()
    spec_text = example_system_specification()
    
    print("=== 语法检查 ===")
    syntax_result = language.check_syntax(spec_text)
    print(f"语法正确: {syntax_result['valid']}")
    if not syntax_result['valid']:
        for error in syntax_result['errors']:
            print(f"错误: {error}")


if __name__ == "__main__":
    test_language()
