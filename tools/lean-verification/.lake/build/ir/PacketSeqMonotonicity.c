// Lean compiler output
// Module: PacketSeqMonotonicity
// Imports: public import Init public meta import Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
static const lean_string_object lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__0_value;
static const lean_string_object lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "seq"};
static const lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__1 = (const lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__1_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__1_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__2 = (const lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__2_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__2_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__3 = (const lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__3_value;
static const lean_string_object lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__4 = (const lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__4_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__4_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__5 = (const lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__5_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__3_value),((lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__5_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__6 = (const lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__6_value;
static lean_once_cell_t lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__7;
static const lean_string_object lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__8 = (const lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__8_value;
static lean_once_cell_t lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__9;
static lean_once_cell_t lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__10;
static const lean_ctor_object lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__0_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__11 = (const lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__11_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__8_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__12 = (const lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__12_value;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprPacket_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprPacket_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_SystemOSIOTLean_instReprPacket___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SystemOSIOTLean_instReprPacket_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SystemOSIOTLean_instReprPacket___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instReprPacket___closed__0_value;
LEAN_EXPORT const lean_object* lp_SystemOSIOTLean_instReprPacket = (const lean_object*)&lp_SystemOSIOTLean_instReprPacket___closed__0_value;
LEAN_EXPORT uint8_t lp_SystemOSIOTLean_instBEqPacket_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instBEqPacket_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_SystemOSIOTLean_instBEqPacket___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SystemOSIOTLean_instBEqPacket_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SystemOSIOTLean_instBEqPacket___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instBEqPacket___closed__0_value;
LEAN_EXPORT const lean_object* lp_SystemOSIOTLean_instBEqPacket = (const lean_object*)&lp_SystemOSIOTLean_instBEqPacket___closed__0_value;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instInhabitedPacket_default;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instInhabitedPacket;
static const lean_string_object lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nextSeq"};
static const lean_object* lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__0_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__0_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__1 = (const lean_object*)&lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__1_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__1_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__2 = (const lean_object*)&lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__2_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__2_value),((lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__5_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__3 = (const lean_object*)&lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__3_value;
static lean_once_cell_t lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__4;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprSenderState_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprSenderState_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprSenderState_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_SystemOSIOTLean_instReprSenderState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SystemOSIOTLean_instReprSenderState_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SystemOSIOTLean_instReprSenderState___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instReprSenderState___closed__0_value;
LEAN_EXPORT const lean_object* lp_SystemOSIOTLean_instReprSenderState = (const lean_object*)&lp_SystemOSIOTLean_instReprSenderState___closed__0_value;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instInhabitedSenderState_default;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instInhabitedSenderState;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00instReprNetworkState_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00instReprNetworkState_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Std_Format_joinSep___at___00List_repr___at___00instReprNetworkState_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__1 = (const lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__1_value;
static const lean_string_object lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__2 = (const lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__2_value;
static const lean_string_object lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__3 = (const lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__3_value;
static const lean_ctor_object lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__3_value)}};
static const lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__4 = (const lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__4_value;
static const lean_ctor_object lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__5 = (const lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__5_value;
static const lean_string_object lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__6 = (const lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__6_value;
static lean_once_cell_t lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__7;
static lean_once_cell_t lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__8;
static const lean_ctor_object lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__9 = (const lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__9_value;
static const lean_ctor_object lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__6_value)}};
static const lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__10 = (const lean_object*)&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__10_value;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg(lean_object*);
static const lean_string_object lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "sender"};
static const lean_object* lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__0_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__0_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__1 = (const lean_object*)&lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__1_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__1_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__2 = (const lean_object*)&lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__2_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__2_value),((lean_object*)&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__5_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__3 = (const lean_object*)&lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__3_value;
static lean_once_cell_t lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__4;
static const lean_string_object lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "channel"};
static const lean_object* lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__5 = (const lean_object*)&lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__5_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__5_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__6 = (const lean_object*)&lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprNetworkState_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprNetworkState_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprNetworkState_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_SystemOSIOTLean_instReprNetworkState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SystemOSIOTLean_instReprNetworkState_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SystemOSIOTLean_instReprNetworkState___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instReprNetworkState___closed__0_value;
LEAN_EXPORT const lean_object* lp_SystemOSIOTLean_instReprNetworkState = (const lean_object*)&lp_SystemOSIOTLean_instReprNetworkState___closed__0_value;
static const lean_ctor_object lp_SystemOSIOTLean_instInhabitedNetworkState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_SystemOSIOTLean_instInhabitedNetworkState_default___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instInhabitedNetworkState_default___closed__0_value;
LEAN_EXPORT const lean_object* lp_SystemOSIOTLean_instInhabitedNetworkState_default = (const lean_object*)&lp_SystemOSIOTLean_instInhabitedNetworkState_default___closed__0_value;
LEAN_EXPORT const lean_object* lp_SystemOSIOTLean_instInhabitedNetworkState = (const lean_object*)&lp_SystemOSIOTLean_instInhabitedNetworkState_default___closed__0_value;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_List_mapTR_loop___at___00seqs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_seqs(lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean___private_PacketSeqMonotonicity_0__nondecreasing_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean___private_PacketSeqMonotonicity_0__nondecreasing_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_unsigned_to_nat(7u);
v___x_15_ = lean_nat_to_int(v___x_14_);
return v___x_15_;
}
}
static lean_object* _init_lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__9(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = ((lean_object*)(lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__0));
v___x_18_ = lean_string_length(v___x_17_);
return v___x_18_;
}
}
static lean_object* _init_lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__10(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_19_ = lean_obj_once(&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__9, &lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__9_once, _init_lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__9);
v___x_20_ = lean_nat_to_int(v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprPacket_repr___redArg(lean_object* v_x_25_){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; uint8_t v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_26_ = ((lean_object*)(lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__6));
v___x_27_ = lean_obj_once(&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__7, &lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__7_once, _init_lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__7);
v___x_28_ = l_Nat_reprFast(v_x_25_);
v___x_29_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
v___x_30_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_27_);
lean_ctor_set(v___x_30_, 1, v___x_29_);
v___x_31_ = 0;
v___x_32_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_32_, 0, v___x_30_);
lean_ctor_set_uint8(v___x_32_, sizeof(void*)*1, v___x_31_);
v___x_33_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_26_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
v___x_34_ = lean_obj_once(&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__10, &lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__10_once, _init_lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__10);
v___x_35_ = ((lean_object*)(lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__11));
v___x_36_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_33_);
v___x_37_ = ((lean_object*)(lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__12));
v___x_38_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_36_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
v___x_39_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_34_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
v___x_40_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set_uint8(v___x_40_, sizeof(void*)*1, v___x_31_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprPacket_repr(lean_object* v_x_41_, lean_object* v_prec_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lp_SystemOSIOTLean_instReprPacket_repr___redArg(v_x_41_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprPacket_repr___boxed(lean_object* v_x_44_, lean_object* v_prec_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = lp_SystemOSIOTLean_instReprPacket_repr(v_x_44_, v_prec_45_);
lean_dec(v_prec_45_);
return v_res_46_;
}
}
LEAN_EXPORT uint8_t lp_SystemOSIOTLean_instBEqPacket_beq(lean_object* v_x_49_, lean_object* v_x_50_){
_start:
{
uint8_t v___x_51_; 
v___x_51_ = lean_nat_dec_eq(v_x_49_, v_x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instBEqPacket_beq___boxed(lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = lp_SystemOSIOTLean_instBEqPacket_beq(v_x_52_, v_x_53_);
lean_dec(v_x_53_);
lean_dec(v_x_52_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
static lean_object* _init_lp_SystemOSIOTLean_instInhabitedPacket_default(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_unsigned_to_nat(0u);
return v___x_58_;
}
}
static lean_object* _init_lp_SystemOSIOTLean_instInhabitedPacket(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_unsigned_to_nat(0u);
return v___x_59_;
}
}
static lean_object* _init_lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_unsigned_to_nat(11u);
v___x_70_ = lean_nat_to_int(v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprSenderState_repr___redArg(lean_object* v_x_71_){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; uint8_t v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_72_ = ((lean_object*)(lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__3));
v___x_73_ = lean_obj_once(&lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__4, &lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__4_once, _init_lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__4);
v___x_74_ = l_Nat_reprFast(v_x_71_);
v___x_75_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_75_, 0, v___x_74_);
v___x_76_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_73_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = 0;
v___x_78_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_78_, 0, v___x_76_);
lean_ctor_set_uint8(v___x_78_, sizeof(void*)*1, v___x_77_);
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_72_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_obj_once(&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__10, &lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__10_once, _init_lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__10);
v___x_81_ = ((lean_object*)(lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__11));
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
lean_ctor_set(v___x_82_, 1, v___x_79_);
v___x_83_ = ((lean_object*)(lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__12));
v___x_84_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_80_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_77_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprSenderState_repr(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lp_SystemOSIOTLean_instReprSenderState_repr___redArg(v_x_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprSenderState_repr___boxed(lean_object* v_x_90_, lean_object* v_prec_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = lp_SystemOSIOTLean_instReprSenderState_repr(v_x_90_, v_prec_91_);
lean_dec(v_prec_91_);
return v_res_92_;
}
}
static lean_object* _init_lp_SystemOSIOTLean_instInhabitedSenderState_default(void){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_unsigned_to_nat(0u);
return v___x_95_;
}
}
static lean_object* _init_lp_SystemOSIOTLean_instInhabitedSenderState(void){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_unsigned_to_nat(0u);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00instReprNetworkState_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_97_, lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
lean_dec(v_x_97_);
return v_x_98_;
}
else
{
lean_object* v_head_100_; lean_object* v_tail_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_111_; 
v_head_100_ = lean_ctor_get(v_x_99_, 0);
v_tail_101_ = lean_ctor_get(v_x_99_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v_x_99_);
if (v_isSharedCheck_111_ == 0)
{
v___x_103_ = v_x_99_;
v_isShared_104_ = v_isSharedCheck_111_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_tail_101_);
lean_inc(v_head_100_);
lean_dec(v_x_99_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_111_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
lean_inc(v_x_97_);
if (v_isShared_104_ == 0)
{
lean_ctor_set_tag(v___x_103_, 5);
lean_ctor_set(v___x_103_, 1, v_x_97_);
lean_ctor_set(v___x_103_, 0, v_x_98_);
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_x_98_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_x_97_);
v___x_106_ = v_reuseFailAlloc_110_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lp_SystemOSIOTLean_instReprPacket_repr___redArg(v_head_100_);
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v_x_98_ = v___x_108_;
v_x_99_ = v_tail_101_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00instReprNetworkState_repr_spec__0_spec__0_spec__1(lean_object* v_x_112_, lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
if (lean_obj_tag(v_x_114_) == 0)
{
lean_dec(v_x_112_);
return v_x_113_;
}
else
{
lean_object* v_head_115_; lean_object* v_tail_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_126_; 
v_head_115_ = lean_ctor_get(v_x_114_, 0);
v_tail_116_ = lean_ctor_get(v_x_114_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_x_114_);
if (v_isSharedCheck_126_ == 0)
{
v___x_118_ = v_x_114_;
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_tail_116_);
lean_inc(v_head_115_);
lean_dec(v_x_114_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_126_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
lean_inc(v_x_112_);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 5);
lean_ctor_set(v___x_118_, 1, v_x_112_);
lean_ctor_set(v___x_118_, 0, v_x_113_);
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_x_113_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_x_112_);
v___x_121_ = v_reuseFailAlloc_125_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_122_ = lp_SystemOSIOTLean_instReprPacket_repr___redArg(v_head_115_);
v___x_123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = lp_SystemOSIOTLean_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00instReprNetworkState_repr_spec__0_spec__0_spec__1_spec__2(v_x_112_, v___x_123_, v_tail_116_);
return v___x_124_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Std_Format_joinSep___at___00List_repr___at___00instReprNetworkState_repr_spec__0_spec__0(lean_object* v_x_127_, lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v___x_129_; 
lean_dec(v_x_128_);
v___x_129_ = lean_box(0);
return v___x_129_;
}
else
{
lean_object* v_tail_130_; 
v_tail_130_ = lean_ctor_get(v_x_127_, 1);
if (lean_obj_tag(v_tail_130_) == 0)
{
lean_object* v_head_131_; lean_object* v___x_132_; 
lean_dec(v_x_128_);
v_head_131_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_head_131_);
lean_dec_ref_known(v_x_127_, 2);
v___x_132_ = lp_SystemOSIOTLean_instReprPacket_repr___redArg(v_head_131_);
return v___x_132_;
}
else
{
lean_object* v_head_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
lean_inc(v_tail_130_);
v_head_133_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_head_133_);
lean_dec_ref_known(v_x_127_, 2);
v___x_134_ = lp_SystemOSIOTLean_instReprPacket_repr___redArg(v_head_133_);
v___x_135_ = lp_SystemOSIOTLean_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00instReprNetworkState_repr_spec__0_spec__0_spec__1(v_x_128_, v___x_134_, v_tail_130_);
return v___x_135_;
}
}
}
}
static lean_object* _init_lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__7(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__2));
v___x_148_ = lean_string_length(v___x_147_);
return v___x_148_;
}
}
static lean_object* _init_lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__8(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = lean_obj_once(&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__7, &lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__7_once, _init_lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__7);
v___x_150_ = lean_nat_to_int(v___x_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg(lean_object* v_a_155_){
_start:
{
if (lean_obj_tag(v_a_155_) == 0)
{
lean_object* v___x_156_; 
v___x_156_ = ((lean_object*)(lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__1));
return v___x_156_;
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; 
v___x_157_ = ((lean_object*)(lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__5));
v___x_158_ = lp_SystemOSIOTLean_Std_Format_joinSep___at___00List_repr___at___00instReprNetworkState_repr_spec__0_spec__0(v_a_155_, v___x_157_);
v___x_159_ = lean_obj_once(&lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__8, &lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__8_once, _init_lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__8);
v___x_160_ = ((lean_object*)(lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__9));
v___x_161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_158_);
v___x_162_ = ((lean_object*)(lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__10));
v___x_163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_159_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = 0;
v___x_166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*1, v___x_165_);
return v___x_166_;
}
}
}
static lean_object* _init_lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(10u);
v___x_177_ = lean_nat_to_int(v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprNetworkState_repr___redArg(lean_object* v_x_181_){
_start:
{
lean_object* v_sender_182_; lean_object* v_channel_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_216_; 
v_sender_182_ = lean_ctor_get(v_x_181_, 0);
v_channel_183_ = lean_ctor_get(v_x_181_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v_x_181_);
if (v_isSharedCheck_216_ == 0)
{
v___x_185_ = v_x_181_;
v_isShared_186_ = v_isSharedCheck_216_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_channel_183_);
lean_inc(v_sender_182_);
lean_dec(v_x_181_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_216_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_187_ = ((lean_object*)(lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__5));
v___x_188_ = ((lean_object*)(lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__3));
v___x_189_ = lean_obj_once(&lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__4, &lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__4_once, _init_lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__4);
v___x_190_ = lp_SystemOSIOTLean_instReprSenderState_repr___redArg(v_sender_182_);
if (v_isShared_186_ == 0)
{
lean_ctor_set_tag(v___x_185_, 4);
lean_ctor_set(v___x_185_, 1, v___x_190_);
lean_ctor_set(v___x_185_, 0, v___x_189_);
v___x_192_ = v___x_185_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_189_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_190_);
v___x_192_ = v_reuseFailAlloc_215_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_193_ = 0;
v___x_194_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_194_, 0, v___x_192_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*1, v___x_193_);
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_188_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = ((lean_object*)(lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg___closed__4));
v___x_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = lean_box(1);
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = ((lean_object*)(lp_SystemOSIOTLean_instReprNetworkState_repr___redArg___closed__6));
v___x_201_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v___x_187_);
v___x_203_ = lean_obj_once(&lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__4, &lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__4_once, _init_lp_SystemOSIOTLean_instReprSenderState_repr___redArg___closed__4);
v___x_204_ = lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg(v_channel_183_);
v___x_205_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set_uint8(v___x_206_, sizeof(void*)*1, v___x_193_);
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_202_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_obj_once(&lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__10, &lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__10_once, _init_lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__10);
v___x_209_ = ((lean_object*)(lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__11));
v___x_210_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___x_207_);
v___x_211_ = ((lean_object*)(lp_SystemOSIOTLean_instReprPacket_repr___redArg___closed__12));
v___x_212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_208_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1, v___x_193_);
return v___x_214_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprNetworkState_repr(lean_object* v_x_217_, lean_object* v_prec_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = lp_SystemOSIOTLean_instReprNetworkState_repr___redArg(v_x_217_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprNetworkState_repr___boxed(lean_object* v_x_220_, lean_object* v_prec_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = lp_SystemOSIOTLean_instReprNetworkState_repr(v_x_220_, v_prec_221_);
lean_dec(v_prec_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0(lean_object* v_a_223_, lean_object* v_n_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___redArg(v_a_223_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0___boxed(lean_object* v_a_226_, lean_object* v_n_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = lp_SystemOSIOTLean_List_repr___at___00instReprNetworkState_repr_spec__0(v_a_226_, v_n_227_);
lean_dec(v_n_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_List_mapTR_loop___at___00seqs_spec__0(lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
if (lean_obj_tag(v_a_236_) == 0)
{
lean_object* v___x_238_; 
v___x_238_ = l_List_reverse___redArg(v_a_237_);
return v___x_238_;
}
else
{
lean_object* v_head_239_; lean_object* v_tail_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_248_; 
v_head_239_ = lean_ctor_get(v_a_236_, 0);
v_tail_240_ = lean_ctor_get(v_a_236_, 1);
v_isSharedCheck_248_ = !lean_is_exclusive(v_a_236_);
if (v_isSharedCheck_248_ == 0)
{
v___x_242_ = v_a_236_;
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_tail_240_);
lean_inc(v_head_239_);
lean_dec(v_a_236_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_248_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v_a_237_);
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_head_239_);
lean_ctor_set(v_reuseFailAlloc_247_, 1, v_a_237_);
v___x_245_ = v_reuseFailAlloc_247_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
v_a_236_ = v_tail_240_;
v_a_237_ = v___x_245_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_seqs(lean_object* v_ch_249_){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_box(0);
v___x_251_ = lp_SystemOSIOTLean_List_mapTR_loop___at___00seqs_spec__0(v_ch_249_, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean___private_PacketSeqMonotonicity_0__nondecreasing_match__1_splitter___redArg(lean_object* v_x_252_, lean_object* v_h__1_253_, lean_object* v_h__2_254_, lean_object* v_h__3_255_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec(v_h__3_255_);
lean_dec(v_h__2_254_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_apply_1(v_h__1_253_, v___x_256_);
return v___x_257_;
}
else
{
lean_object* v_tail_258_; 
lean_dec(v_h__1_253_);
v_tail_258_ = lean_ctor_get(v_x_252_, 1);
if (lean_obj_tag(v_tail_258_) == 0)
{
lean_object* v_head_259_; lean_object* v___x_260_; 
lean_dec(v_h__3_255_);
v_head_259_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_head_259_);
lean_dec_ref_known(v_x_252_, 2);
v___x_260_ = lean_apply_1(v_h__2_254_, v_head_259_);
return v___x_260_;
}
else
{
lean_object* v_head_261_; lean_object* v_head_262_; lean_object* v_tail_263_; lean_object* v___x_264_; 
lean_inc_ref(v_tail_258_);
lean_dec(v_h__2_254_);
v_head_261_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_head_261_);
lean_dec_ref_known(v_x_252_, 2);
v_head_262_ = lean_ctor_get(v_tail_258_, 0);
lean_inc(v_head_262_);
v_tail_263_ = lean_ctor_get(v_tail_258_, 1);
lean_inc(v_tail_263_);
lean_dec_ref_known(v_tail_258_, 2);
v___x_264_ = lean_apply_3(v_h__3_255_, v_head_261_, v_head_262_, v_tail_263_);
return v___x_264_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean___private_PacketSeqMonotonicity_0__nondecreasing_match__1_splitter(lean_object* v_motive_265_, lean_object* v_x_266_, lean_object* v_h__1_267_, lean_object* v_h__2_268_, lean_object* v_h__3_269_){
_start:
{
if (lean_obj_tag(v_x_266_) == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec(v_h__3_269_);
lean_dec(v_h__2_268_);
v___x_270_ = lean_box(0);
v___x_271_ = lean_apply_1(v_h__1_267_, v___x_270_);
return v___x_271_;
}
else
{
lean_object* v_tail_272_; 
lean_dec(v_h__1_267_);
v_tail_272_ = lean_ctor_get(v_x_266_, 1);
if (lean_obj_tag(v_tail_272_) == 0)
{
lean_object* v_head_273_; lean_object* v___x_274_; 
lean_dec(v_h__3_269_);
v_head_273_ = lean_ctor_get(v_x_266_, 0);
lean_inc(v_head_273_);
lean_dec_ref_known(v_x_266_, 2);
v___x_274_ = lean_apply_1(v_h__2_268_, v_head_273_);
return v___x_274_;
}
else
{
lean_object* v_head_275_; lean_object* v_head_276_; lean_object* v_tail_277_; lean_object* v___x_278_; 
lean_inc_ref(v_tail_272_);
lean_dec(v_h__2_268_);
v_head_275_ = lean_ctor_get(v_x_266_, 0);
lean_inc(v_head_275_);
lean_dec_ref_known(v_x_266_, 2);
v_head_276_ = lean_ctor_get(v_tail_272_, 0);
lean_inc(v_head_276_);
v_tail_277_ = lean_ctor_get(v_tail_272_, 1);
lean_inc(v_tail_277_);
lean_dec_ref_known(v_tail_272_, 2);
v___x_278_ = lean_apply_3(v_h__3_269_, v_head_275_, v_head_276_, v_tail_277_);
return v___x_278_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SystemOSIOTLean_PacketSeqMonotonicity(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_SystemOSIOTLean_instInhabitedPacket_default = _init_lp_SystemOSIOTLean_instInhabitedPacket_default();
lean_mark_persistent(lp_SystemOSIOTLean_instInhabitedPacket_default);
lp_SystemOSIOTLean_instInhabitedPacket = _init_lp_SystemOSIOTLean_instInhabitedPacket();
lean_mark_persistent(lp_SystemOSIOTLean_instInhabitedPacket);
lp_SystemOSIOTLean_instInhabitedSenderState_default = _init_lp_SystemOSIOTLean_instInhabitedSenderState_default();
lean_mark_persistent(lp_SystemOSIOTLean_instInhabitedSenderState_default);
lp_SystemOSIOTLean_instInhabitedSenderState = _init_lp_SystemOSIOTLean_instInhabitedSenderState();
lean_mark_persistent(lp_SystemOSIOTLean_instInhabitedSenderState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
