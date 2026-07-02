---------------------------- MODULE QUIC ----------------------------
(*
 * SystemOSIOT QUIC / Transport Handshake TLA+ Specification
 * 目标：形式化验证传输层握手协议的基本安全性质。
 * 范围：简化模型，覆盖客户端与服务端的状态机、包交换、握手完成条件。
 * 来源：RFC 9000 (QUIC) / RFC 793 (TCP)。
 * 验证：使用 TLC Model Checker 检查握手安全性。
 *)

EXTENDS Integers, FiniteSets, Naturals

CONSTANTS
    Client,         \* 客户端标识
    Server,         \* 服务端标识
    MaxPacketID     \* 模型检查时最大包编号

ASSUME
    /\ Client # Server
    /\ MaxPacketID \in Nat /\ MaxPacketID > 0

VARIABLES
    state,          \* state[p] : 端点 p 的握手状态
    keysReady,      \* keysReady[p] : 端点 p 是否已准备好加密密钥
    handshakeDone,  \* handshakeDone[p] : 端点 p 是否认为握手完成
    dataAllowed     \* dataAllowed[p] : 端点 p 是否允许发送应用数据

\* 握手状态
InitSent    == "InitSent"      \* 已发送 Initial/ClientHello
InitRcvd    == "InitRcvd"      \* 已收到 Initial
HSSent      == "HSSent"        \* 已发送 Handshake
HSRcvd      == "HSRcvd"        \* 已收到 Handshake
Completed   == "Completed"     \* 握手完成

\* 端点集合
Endpoints == {Client, Server}

vars == <<state, keysReady, handshakeDone, dataAllowed>>

Init ==
    /\ state        = [p \in Endpoints |-> "Idle"]
    /\ keysReady    = [p \in Endpoints |-> FALSE]
    /\ handshakeDone= [p \in Endpoints |-> FALSE]
    /\ dataAllowed   = [p \in Endpoints |-> FALSE]

\* 客户端发送 Initial 包
ClientSendInitial ==
    /\ state[Client] = "Idle"
    /\ state' = [state EXCEPT ![Client] = InitSent]
    /\ UNCHANGED <<keysReady, handshakeDone, dataAllowed>>

\* 服务端收到 Initial 并发送 Handshake 包
ServerRecvInitSendHS ==
    /\ state[Client] = InitSent
    /\ state[Server] = "Idle"
    /\ state' = [state EXCEPT ![Server] = HSSent]
    /\ UNCHANGED <<keysReady, handshakeDone, dataAllowed>>

\* 客户端收到 Handshake 并确认
ClientRecvHSSendACK ==
    /\ state[Server] = HSSent
    /\ state[Client] = InitSent
    /\ state' = [state EXCEPT ![Client] = Completed]
    /\ keysReady' = [keysReady EXCEPT ![Client] = TRUE]
    /\ handshakeDone' = [handshakeDone EXCEPT ![Client] = TRUE]
    /\ dataAllowed' = [dataAllowed EXCEPT ![Client] = TRUE]

\* 服务端收到 ACK 后完成握手
ServerRecvACK ==
    /\ state[Client] = Completed
    /\ state[Server] = HSSent
    /\ state' = [state EXCEPT ![Server] = Completed]
    /\ keysReady' = [keysReady EXCEPT ![Server] = TRUE]
    /\ handshakeDone' = [handshakeDone EXCEPT ![Server] = TRUE]
    /\ dataAllowed' = [dataAllowed EXCEPT ![Server] = TRUE]

\* 下一步迁移关系
Next ==
    \/ ClientSendInitial
    \/ ServerRecvInitSendHS
    \/ ClientRecvHSSendACK
    \/ ServerRecvACK

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------
(* 安全性质 *)

\* 类型不变式
TypeInvariant ==
    /\ state \in [Endpoints -> {"Idle", InitSent, InitRcvd, HSSent, HSRcvd, Completed}]
    /\ keysReady \in [Endpoints -> BOOLEAN]
    /\ handshakeDone \in [Endpoints -> BOOLEAN]
    /\ dataAllowed \in [Endpoints -> BOOLEAN]

\* 握手一致性：若两端都认为握手完成，则状态必须一致
HandshakeConsistency ==
    (handshakeDone[Client] /\ handshakeDone[Server])
        => state[Client] = Completed /\ state[Server] = Completed

\* 无提前数据：在握手完成前不允许发送应用数据
NoDataBeforeHandshake ==
    \A p \in Endpoints : dataAllowed[p] => handshakeDone[p]

\* 密钥就绪先于数据：发送应用数据前必须已准备好密钥
KeysBeforeData ==
    \A p \in Endpoints : dataAllowed[p] => keysReady[p]

=============================================================================
