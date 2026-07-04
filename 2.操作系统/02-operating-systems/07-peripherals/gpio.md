# GPIO

> **权威来源**：Linux Kernel `drivers/gpio/`, pinctrl subsystem docs, Linux Device Drivers。
>
> **目标**：系统讲解 GPIO、pinctrl、gpiochip、中断触发、Linux gpiolib 与用户态接口。

---

## 1. GPIO 基础

| 概念 | 说明 |
|------|------|
| Pin | 物理引脚 |
| Direction | 输入/输出 |
| Value | 高/低电平 |
| Edge | 中断触发边沿 |
| Pull-up/Pull-down | 内部上下拉 |

---

## 2. pinctrl

- 引脚复用控制器（Pin Multiplexer）。
- 一个物理引脚可配置为 GPIO、UART TX、I2C SDA 等功能。

### 2.1 设备树绑定

```dts
pinctrl_mygpio: mygpio {
    fsl,pins = <
        MX6UL_PAD_GPIO1_IO03__GPIO1_IO03 0x10b0
    >;
};

&gpio1 {
    my-led {
        gpios = <&gpio1 3 GPIO_ACTIVE_LOW>;
        label = "my:led";
    };
};
```

---

## 3. Linux gpiolib

### 3.1 核心结构

| 数据结构 | 源码 | 说明 |
|----------|------|------|
| `struct gpio_chip` | `include/linux/gpio/driver.h` | GPIO 控制器 |
| `struct gpio_desc` | `include/linux/gpio/driver.h` | GPIO 描述符 |
| `struct gpio_device` | `include/linux/gpio/driver.h` | GPIO 设备 |

### 3.2 驱动 API

| API | 说明 |
|-----|------|
| `gpiochip_add_data()` | 注册 gpiochip |
| `gpiod_get()` / `gpiod_put()` | 获取/释放 GPIO |
| `gpiod_direction_input()` / `output()` | 设置方向 |
| `gpiod_set_value()` / `get_value()` | 读写电平 |
| `gpiod_to_irq()` | 获取对应 IRQ |

---

## 4. 用户态接口

### 4.1 sysfs（旧）

```bash
echo 3 > /sys/class/gpio/export
echo out > /sys/class/gpio/gpio3/direction
echo 1 > /sys/class/gpio/gpio3/value
```

### 4.2 libgpiod（推荐）

```bash
# 查看芯片
gpiodetect

# 读取
gpioget gpiochip0 3

# 设置
gpioset gpiochip0 3=1

# 监听事件
gpiomon gpiochip0 3
```

---

## 5. GPIO 中断

| 触发方式 | 说明 |
|----------|------|
| IRQ_TYPE_NONE | 无 |
| IRQ_TYPE_EDGE_RISING | 上升沿 |
| IRQ_TYPE_EDGE_FALLING | 下降沿 |
| IRQ_TYPE_EDGE_BOTH | 双边沿 |
| IRQ_TYPE_LEVEL_HIGH | 高电平 |
| IRQ_TYPE_LEVEL_LOW | 低电平 |

---

## 6. 场景分析

| 场景 | 关键参数 | 验证指标 |
|------|----------|----------|
| LED 控制 | 方向，电平 | 响应时间 |
| 按键输入 | 中断触发，消抖 | 误触发率 |
| 继电器控制 | 驱动能力 | 开关可靠性 |
| 传感器状态 | 中断触发 | 事件延迟 |

---

## 7. 术语表

| 中文 | 英文 | 一句话定义 |
|------|------|------------|
| GPIO | General Purpose Input/Output | 通用输入输出 |
| pinctrl | Pin Controller | 引脚复用与电气特性控制器 |
| gpiochip | GPIO Chip | Linux 中 GPIO 控制器抽象 |
| Active Low | 低电平有效 | 0 表示开/真 |
| Active High | 高电平有效 | 1 表示开/真 |

---

## 8. 相关文件

- [外设概念树](./peripheral-concept-tree.md)
- [中断与 DMA](./interrupts-and-dma.md)
