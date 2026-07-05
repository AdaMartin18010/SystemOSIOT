/*
 * SystemOSIOT Alloy IoT Device Access Control Model
 * 目标：验证物联网设备访问控制的角色与权限约束。
 * 内容：设备、用户、角色、权限之间的关系，以及关键安全不变式。
 * 工具：Alloy Analyzer（https://alloytools.org/）。
 */

module IoT_DeviceAccessControl

// 抽象签名
abstract sig Principal {}

sig User extends Principal {}

sig Device {
    // 设备上分配的角色实例：每个角色实例属于一个用户
    assignments : set RoleAssignment
}

// 角色类型
abstract sig Role {}

one sig Admin extends Role {}
one sig Guest extends Role {}
one sig Owner extends Role {}
one sig Operator extends Role {}

// 角色实例：将用户、角色、设备绑定
sig RoleAssignment {
    user : one User,
    role : one Role,
    device : one Device
}

// 权限
abstract sig Permission {}

one sig Read extends Permission {}
one sig Write extends Permission {}
one sig Configure extends Permission {}
one sig Delete extends Permission {}

// 角色到权限的映射
fun rolePermissions[r : Role] : set Permission {
    (r = Admin) => (Read + Write + Configure + Delete) else
    ((r = Owner) => (Read + Write + Configure) else
    ((r = Operator) => (Read + Write) else
    Read))
}

// 约束 1：每个角色实例关联到其所属设备
fact AssignmentConsistency {
    all a : RoleAssignment | a in a.device.assignments
}

// 约束 2：同一设备上，一个用户不能同时拥有 Admin 和 Guest 角色
fact NoAdminAndGuestOnSameDevice {
    all d : Device, u : User |
        (some a1 : d.assignments | a1.user = u and a1.role = Admin)
        implies
        (no a2 : d.assignments | a2.user = u and a2.role = Guest)
}

// 约束 3：每个设备至少有一个 Owner
fact EveryDeviceHasOwner {
    all d : Device |
        some a : d.assignments | a.role = Owner
}

// 约束 4：Owner 权限是 Admin 权限的子集（Admin 拥有 Owner 的所有权限）
fact AdminImpliesFullControl {
    all d : Device, a : d.assignments |
        a.role = Admin implies rolePermissions[Owner] in rolePermissions[Admin]
}

// 断言 1：不存在同一用户在同一设备上同时拥有 Admin 和 Guest
assert NoConflictingRoles {
    no disj a1, a2 : RoleAssignment |
        a1.user = a2.user
        and a1.device = a2.device
        and a1.role = Admin
        and a2.role = Guest
}

// 断言 2：每个设备至少有一个 Owner
assert EveryDeviceHasAtLeastOneOwner {
    all d : Device | some a : d.assignments | a.role = Owner
}

// 断言 3：Guest 不拥有写权限
assert GuestCannotWrite {
    all a : RoleAssignment |
        a.role = Guest implies Write not in rolePermissions[a.role]
}

// 运行检查
check NoConflictingRoles for 5
check EveryDeviceHasAtLeastOneOwner for 5
check GuestCannotWrite for 5

// 示例场景：2 个设备，3 个用户，至少 1 个 Admin 和 1 个 Guest
pred ShowExample {
    #Device = 2
    #User = 3
    some a : RoleAssignment | a.role = Admin
    some a : RoleAssignment | a.role = Guest
}

run ShowExample for 20 but exactly 2 Device, exactly 3 User
