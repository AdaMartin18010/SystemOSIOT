// SystemOSIOT PRISM Example
// 目标：验证两进程互斥协议的安全性与活性（MDP 模型）。
// 运行：prism Mutex.pm -pf 'filter(forall, G !(s1=2 & s2=2))'

mdp

module Process1
  s1 : [0..2] init 0; // 0=idle, 1=waiting, 2=critical
  [req1] s1=0 -> (s1'=1);
  [enter1] s1=1 & s2!=2 -> (s1'=2);
  [exit1] s1=2 -> (s1'=0);
endmodule

module Process2
  s2 : [0..2] init 0;
  [req2] s2=0 -> (s2'=1);
  [enter2] s2=1 & s1!=2 -> (s2'=2);
  [exit2] s2=2 -> (s2'=0);
endmodule

// 安全性质：不存在两进程同时处于临界区的状态
label "unsafe" = s1=2 & s2=2;

// 活性性质：进程 1 等待时最终能进入临界区（概率最大值 = 1）
label "p1_waiting" = s1=1;
label "p1_critical" = s1=2;
