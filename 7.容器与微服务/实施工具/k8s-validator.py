#!/usr/bin/env python3
"""
Kubernetes配置验证工具
Kubernetes Configuration Validator

功能：
- 验证Kubernetes YAML配置文件的语法和语义
- 检查资源限制和请求的合理性
- 验证安全配置和最佳实践
- 生成配置优化建议

作者：容器微服务系统分析项目组
版本：v1.0
日期：2024-12-19
"""

import yaml
import json
import sys
import argparse
import re
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass
from enum import Enum
import logging

# 配置日志
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

class ValidationLevel(Enum):
    """验证级别"""
    ERROR = "error"
    WARNING = "warning"
    INFO = "info"

@dataclass
class ValidationResult:
    """验证结果"""
    level: ValidationLevel
    message: str
    resource: str
    field: str
    suggestion: Optional[str] = None

class K8sValidator:
    """Kubernetes配置验证器"""
    
    def __init__(self):
        self.results: List[ValidationResult] = []
        self.resource_limits = {
            'cpu': {'min': '10m', 'max': '8', 'default': '100m'},
            'memory': {'min': '32Mi', 'max': '32Gi', 'default': '128Mi'}
        }
        
    def validate_file(self, file_path: str) -> List[ValidationResult]:
        """验证Kubernetes配置文件"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 支持多文档YAML
            documents = list(yaml.safe_load_all(content))
            
            for i, doc in enumerate(documents):
                if doc is None:
                    continue
                    
                doc_name = f"Document {i+1}"
                self._validate_document(doc, doc_name)
                
        except yaml.YAMLError as e:
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message=f"YAML语法错误: {str(e)}",
                resource="文件",
                field="语法"
            ))
        except FileNotFoundError:
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message=f"文件不存在: {file_path}",
                resource="文件",
                field="路径"
            ))
            
        return self.results
    
    def _validate_document(self, doc: Dict[str, Any], doc_name: str):
        """验证单个Kubernetes文档"""
        if not isinstance(doc, dict):
            return
            
        api_version = doc.get('apiVersion', '')
        kind = doc.get('kind', '')
        metadata = doc.get('metadata', {})
        name = metadata.get('name', 'unknown')
        
        resource_name = f"{kind}/{name}" if name != 'unknown' else f"{kind}"
        
        # 基础验证
        self._validate_basic_fields(doc, resource_name)
        
        # 根据资源类型进行特定验证
        if kind == 'Pod':
            self._validate_pod(doc, resource_name)
        elif kind == 'Deployment':
            self._validate_deployment(doc, resource_name)
        elif kind == 'Service':
            self._validate_service(doc, resource_name)
        elif kind == 'ConfigMap':
            self._validate_configmap(doc, resource_name)
        elif kind == 'Secret':
            self._validate_secret(doc, resource_name)
        elif kind == 'Ingress':
            self._validate_ingress(doc, resource_name)
        elif kind == 'NetworkPolicy':
            self._validate_network_policy(doc, resource_name)
        elif kind == 'PersistentVolumeClaim':
            self._validate_pvc(doc, resource_name)
            
    def _validate_basic_fields(self, doc: Dict[str, Any], resource_name: str):
        """验证基础字段"""
        required_fields = ['apiVersion', 'kind', 'metadata']
        
        for field in required_fields:
            if field not in doc:
                self.results.append(ValidationResult(
                    level=ValidationLevel.ERROR,
                    message=f"缺少必需字段: {field}",
                    resource=resource_name,
                    field=field
                ))
        
        # 验证metadata
        metadata = doc.get('metadata', {})
        if 'name' not in metadata:
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message="metadata中缺少name字段",
                resource=resource_name,
                field="metadata.name"
            ))
            
        # 验证标签
        labels = metadata.get('labels', {})
        if not labels:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="建议添加labels以便资源管理",
                resource=resource_name,
                field="metadata.labels",
                suggestion="添加app, version, environment等标签"
            ))
    
    def _validate_pod(self, doc: Dict[str, Any], resource_name: str):
        """验证Pod配置"""
        spec = doc.get('spec', {})
        containers = spec.get('containers', [])
        
        if not containers:
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message="Pod必须包含至少一个容器",
                resource=resource_name,
                field="spec.containers"
            ))
            return
            
        for i, container in enumerate(containers):
            container_name = container.get('name', f'container-{i}')
            self._validate_container(container, f"{resource_name}/{container_name}")
            
        # 验证Pod安全配置
        self._validate_pod_security(spec, resource_name)
        
    def _validate_container(self, container: Dict[str, Any], container_name: str):
        """验证容器配置"""
        # 验证镜像
        image = container.get('image', '')
        if not image:
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message="容器必须指定镜像",
                resource=container_name,
                field="image"
            ))
        elif 'latest' in image:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="不建议使用latest标签",
                resource=container_name,
                field="image",
                suggestion="使用具体的版本标签，如v1.2.3"
            ))
            
        # 验证资源限制
        resources = container.get('resources', {})
        self._validate_resources(resources, container_name)
        
        # 验证安全配置
        security_context = container.get('securityContext', {})
        self._validate_security_context(security_context, container_name)
        
        # 验证健康检查
        self._validate_health_checks(container, container_name)
        
    def _validate_resources(self, resources: Dict[str, Any], container_name: str):
        """验证资源配置"""
        limits = resources.get('limits', {})
        requests = resources.get('requests', {})
        
        # 检查是否设置了资源限制
        if not limits and not requests:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="建议设置资源限制和请求",
                resource=container_name,
                field="resources",
                suggestion="设置CPU和内存的limits和requests"
            ))
            
        # 验证CPU配置
        cpu_limit = limits.get('cpu', '')
        cpu_request = requests.get('cpu', '')
        
        if cpu_limit and not self._is_valid_cpu_value(cpu_limit):
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message=f"无效的CPU限制值: {cpu_limit}",
                resource=container_name,
                field="resources.limits.cpu",
                suggestion="使用格式如100m, 0.5, 1等"
            ))
            
        if cpu_request and not self._is_valid_cpu_value(cpu_request):
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message=f"无效的CPU请求值: {cpu_request}",
                resource=container_name,
                field="resources.requests.cpu",
                suggestion="使用格式如100m, 0.5, 1等"
            ))
            
        # 验证内存配置
        memory_limit = limits.get('memory', '')
        memory_request = requests.get('memory', '')
        
        if memory_limit and not self._is_valid_memory_value(memory_limit):
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message=f"无效的内存限制值: {memory_limit}",
                resource=container_name,
                field="resources.limits.memory",
                suggestion="使用格式如128Mi, 1Gi等"
            ))
            
        if memory_request and not self._is_valid_memory_value(memory_request):
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message=f"无效的内存请求值: {memory_request}",
                resource=container_name,
                field="resources.requests.memory",
                suggestion="使用格式如128Mi, 1Gi等"
            ))
    
    def _validate_security_context(self, security_context: Dict[str, Any], container_name: str):
        """验证安全上下文"""
        # 检查是否以root用户运行
        run_as_user = security_context.get('runAsUser')
        if run_as_user is None:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="建议设置runAsUser避免以root用户运行",
                resource=container_name,
                field="securityContext.runAsUser",
                suggestion="设置非root用户ID，如1000"
            ))
        elif run_as_user == 0:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="容器以root用户运行存在安全风险",
                resource=container_name,
                field="securityContext.runAsUser",
                suggestion="使用非root用户ID"
            ))
            
        # 检查特权模式
        privileged = security_context.get('privileged', False)
        if privileged:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="特权模式存在安全风险",
                resource=container_name,
                field="securityContext.privileged",
                suggestion="避免使用特权模式，除非必要"
            ))
            
        # 检查只读根文件系统
        read_only_root_filesystem = security_context.get('readOnlyRootFilesystem', False)
        if not read_only_root_filesystem:
            self.results.append(ValidationResult(
                level=ValidationLevel.INFO,
                message="建议启用只读根文件系统",
                resource=container_name,
                field="securityContext.readOnlyRootFilesystem",
                suggestion="设置readOnlyRootFilesystem: true"
            ))
    
    def _validate_health_checks(self, container: Dict[str, Any], container_name: str):
        """验证健康检查配置"""
        # 检查存活探针
        liveness_probe = container.get('livenessProbe')
        if not liveness_probe:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="建议配置存活探针",
                resource=container_name,
                field="livenessProbe",
                suggestion="配置HTTP、TCP或命令探针"
            ))
            
        # 检查就绪探针
        readiness_probe = container.get('readinessProbe')
        if not readiness_probe:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="建议配置就绪探针",
                resource=container_name,
                field="readinessProbe",
                suggestion="配置HTTP、TCP或命令探针"
            ))
    
    def _validate_pod_security(self, spec: Dict[str, Any], resource_name: str):
        """验证Pod安全配置"""
        # 检查服务账户
        service_account = spec.get('serviceAccountName')
        if not service_account:
            self.results.append(ValidationResult(
                level=ValidationLevel.INFO,
                message="建议指定服务账户",
                resource=resource_name,
                field="spec.serviceAccountName",
                suggestion="创建专用的服务账户"
            ))
            
        # 检查安全上下文
        security_context = spec.get('securityContext', {})
        run_as_non_root = security_context.get('runAsNonRoot', False)
        if not run_as_non_root:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="建议设置runAsNonRoot: true",
                resource=resource_name,
                field="spec.securityContext.runAsNonRoot",
                suggestion="提高Pod安全性"
            ))
    
    def _validate_deployment(self, doc: Dict[str, Any], resource_name: str):
        """验证Deployment配置"""
        spec = doc.get('spec', {})
        
        # 检查副本数
        replicas = spec.get('replicas', 1)
        if replicas < 1:
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message="副本数必须大于0",
                resource=resource_name,
                field="spec.replicas"
            ))
        elif replicas == 1:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="单副本部署存在可用性风险",
                resource=resource_name,
                field="spec.replicas",
                suggestion="考虑增加副本数以提高可用性"
            ))
            
        # 检查更新策略
        strategy = spec.get('strategy', {})
        strategy_type = strategy.get('type', 'RollingUpdate')
        if strategy_type not in ['RollingUpdate', 'Recreate']:
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message=f"无效的更新策略: {strategy_type}",
                resource=resource_name,
                field="spec.strategy.type",
                suggestion="使用RollingUpdate或Recreate"
            ))
    
    def _validate_service(self, doc: Dict[str, Any], resource_name: str):
        """验证Service配置"""
        spec = doc.get('spec', {})
        
        # 检查端口配置
        ports = spec.get('ports', [])
        if not ports:
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message="Service必须配置端口",
                resource=resource_name,
                field="spec.ports"
            ))
            
        for i, port in enumerate(ports):
            port_name = f"port-{i}"
            if 'port' not in port:
                self.results.append(ValidationResult(
                    level=ValidationLevel.ERROR,
                    message="端口配置缺少port字段",
                    resource=resource_name,
                    field=f"spec.ports[{i}].port"
                ))
                
        # 检查选择器
        selector = spec.get('selector', {})
        if not selector:
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message="Service必须配置选择器",
                resource=resource_name,
                field="spec.selector"
            ))
    
    def _validate_configmap(self, doc: Dict[str, Any], resource_name: str):
        """验证ConfigMap配置"""
        data = doc.get('data', {})
        if not data:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="ConfigMap为空",
                resource=resource_name,
                field="data",
                suggestion="添加配置数据或删除空的ConfigMap"
            ))
    
    def _validate_secret(self, doc: Dict[str, Any], resource_name: str):
        """验证Secret配置"""
        data = doc.get('data', {})
        string_data = doc.get('stringData', {})
        
        if not data and not string_data:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="Secret为空",
                resource=resource_name,
                field="data/stringData",
                suggestion="添加敏感数据或删除空的Secret"
            ))
            
        # 检查是否使用了不安全的类型
        secret_type = doc.get('type', 'Opaque')
        if secret_type == 'Opaque':
            self.results.append(ValidationResult(
                level=ValidationLevel.INFO,
                message="建议使用具体的Secret类型",
                resource=resource_name,
                field="type",
                suggestion="使用kubernetes.io/tls, kubernetes.io/dockerconfigjson等"
            ))
    
    def _validate_ingress(self, doc: Dict[str, Any], resource_name: str):
        """验证Ingress配置"""
        spec = doc.get('spec', {})
        
        # 检查规则
        rules = spec.get('rules', [])
        if not rules:
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message="Ingress必须配置规则",
                resource=resource_name,
                field="spec.rules"
            ))
            
        # 检查TLS配置
        tls = spec.get('tls', [])
        if not tls:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="建议配置TLS加密",
                resource=resource_name,
                field="spec.tls",
                suggestion="配置HTTPS证书"
            ))
    
    def _validate_network_policy(self, doc: Dict[str, Any], resource_name: str):
        """验证NetworkPolicy配置"""
        spec = doc.get('spec', {})
        
        # 检查pod选择器
        pod_selector = spec.get('podSelector', {})
        if not pod_selector:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="NetworkPolicy缺少pod选择器",
                resource=resource_name,
                field="spec.podSelector",
                suggestion="配置pod选择器以指定策略适用范围"
            ))
    
    def _validate_pvc(self, doc: Dict[str, Any], resource_name: str):
        """验证PersistentVolumeClaim配置"""
        spec = doc.get('spec', {})
        
        # 检查存储类
        storage_class = spec.get('storageClassName', '')
        if not storage_class:
            self.results.append(ValidationResult(
                level=ValidationLevel.WARNING,
                message="建议指定存储类",
                resource=resource_name,
                field="spec.storageClassName",
                suggestion="选择合适的存储类"
            ))
            
        # 检查访问模式
        access_modes = spec.get('accessModes', [])
        if not access_modes:
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message="必须指定访问模式",
                resource=resource_name,
                field="spec.accessModes"
            ))
            
        # 检查资源请求
        resources = spec.get('resources', {})
        requests = resources.get('requests', {})
        storage = requests.get('storage', '')
        if not storage:
            self.results.append(ValidationResult(
                level=ValidationLevel.ERROR,
                message="必须指定存储大小",
                resource=resource_name,
                field="spec.resources.requests.storage"
            ))
    
    def _is_valid_cpu_value(self, value: str) -> bool:
        """验证CPU值格式"""
        # 支持格式: 100m, 0.5, 1, 1000m等
        pattern = r'^(\d+(\.\d+)?)(m)?$'
        return bool(re.match(pattern, str(value)))
    
    def _is_valid_memory_value(self, value: str) -> bool:
        """验证内存值格式"""
        # 支持格式: 128Mi, 1Gi, 1000M等
        pattern = r'^\d+(\.\d+)?(Ki|Mi|Gi|Ti|Pi|Ei|K|M|G|T|P|E)?$'
        return bool(re.match(pattern, str(value)))
    
    def generate_report(self) -> str:
        """生成验证报告"""
        if not self.results:
            return "✅ 所有配置验证通过！"
            
        report = ["# Kubernetes配置验证报告\n"]
        
        # 按级别分组
        errors = [r for r in self.results if r.level == ValidationLevel.ERROR]
        warnings = [r for r in self.results if r.level == ValidationLevel.WARNING]
        infos = [r for r in self.results if r.level == ValidationLevel.INFO]
        
        if errors:
            report.append("## ❌ 错误 (Errors)")
            for result in errors:
                report.append(f"- **{result.resource}**: {result.message}")
                if result.suggestion:
                    report.append(f"  💡 建议: {result.suggestion}")
                report.append("")
                
        if warnings:
            report.append("## ⚠️ 警告 (Warnings)")
            for result in warnings:
                report.append(f"- **{result.resource}**: {result.message}")
                if result.suggestion:
                    report.append(f"  💡 建议: {result.suggestion}")
                report.append("")
                
        if infos:
            report.append("## ℹ️ 信息 (Info)")
            for result in infos:
                report.append(f"- **{result.resource}**: {result.message}")
                if result.suggestion:
                    report.append(f"  💡 建议: {result.suggestion}")
                report.append("")
        
        # 统计信息
        report.append("## 📊 统计信息")
        report.append(f"- 总检查项: {len(self.results)}")
        report.append(f"- 错误: {len(errors)}")
        report.append(f"- 警告: {len(warnings)}")
        report.append(f"- 信息: {len(infos)}")
        
        return "\n".join(report)

def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='Kubernetes配置验证工具')
    parser.add_argument('files', nargs='+', help='要验证的Kubernetes YAML文件')
    parser.add_argument('--output', '-o', help='输出报告文件路径')
    parser.add_argument('--format', choices=['text', 'json'], default='text', help='输出格式')
    parser.add_argument('--verbose', '-v', action='store_true', help='详细输出')
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
    
    validator = K8sValidator()
    
    for file_path in args.files:
        logger.info(f"验证文件: {file_path}")
        validator.validate_file(file_path)
    
    # 生成报告
    if args.format == 'json':
        report = json.dumps([{
            'level': r.level.value,
            'message': r.message,
            'resource': r.resource,
            'field': r.field,
            'suggestion': r.suggestion
        } for r in validator.results], indent=2, ensure_ascii=False)
    else:
        report = validator.generate_report()
    
    # 输出报告
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as f:
            f.write(report)
        logger.info(f"报告已保存到: {args.output}")
    else:
        print(report)
    
    # 返回退出码
    error_count = len([r for r in validator.results if r.level == ValidationLevel.ERROR])
    sys.exit(error_count)

if __name__ == '__main__':
    main()
