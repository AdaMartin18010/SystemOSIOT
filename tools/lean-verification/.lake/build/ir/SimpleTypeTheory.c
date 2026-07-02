// Lean compiler output
// Module: SimpleTypeTheory
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ifz_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ifz_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_SystemOSIOTLean_instReprExpr_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Expr.num"};
static const lean_object* lp_SystemOSIOTLean_instReprExpr_repr___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__0_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprExpr_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__0_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprExpr_repr___closed__1 = (const lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__1_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprExpr_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_SystemOSIOTLean_instReprExpr_repr___closed__2 = (const lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__2_value;
static lean_once_cell_t lp_SystemOSIOTLean_instReprExpr_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SystemOSIOTLean_instReprExpr_repr___closed__3;
static lean_once_cell_t lp_SystemOSIOTLean_instReprExpr_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_SystemOSIOTLean_instReprExpr_repr___closed__4;
static const lean_string_object lp_SystemOSIOTLean_instReprExpr_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Expr.add"};
static const lean_object* lp_SystemOSIOTLean_instReprExpr_repr___closed__5 = (const lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__5_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprExpr_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__5_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprExpr_repr___closed__6 = (const lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__6_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprExpr_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_SystemOSIOTLean_instReprExpr_repr___closed__7 = (const lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__7_value;
static const lean_string_object lp_SystemOSIOTLean_instReprExpr_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Expr.ifz"};
static const lean_object* lp_SystemOSIOTLean_instReprExpr_repr___closed__8 = (const lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__8_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprExpr_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__8_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprExpr_repr___closed__9 = (const lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__9_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprExpr_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_SystemOSIOTLean_instReprExpr_repr___closed__10 = (const lean_object*)&lp_SystemOSIOTLean_instReprExpr_repr___closed__10_value;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprExpr_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprExpr_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_SystemOSIOTLean_instReprExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SystemOSIOTLean_instReprExpr_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SystemOSIOTLean_instReprExpr___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instReprExpr___closed__0_value;
LEAN_EXPORT const lean_object* lp_SystemOSIOTLean_instReprExpr = (const lean_object*)&lp_SystemOSIOTLean_instReprExpr___closed__0_value;
static const lean_string_object lp_SystemOSIOTLean_instReprValue_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Value.vnum"};
static const lean_object* lp_SystemOSIOTLean_instReprValue_repr___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instReprValue_repr___closed__0_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprValue_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprValue_repr___closed__0_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprValue_repr___closed__1 = (const lean_object*)&lp_SystemOSIOTLean_instReprValue_repr___closed__1_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprValue_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprValue_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_SystemOSIOTLean_instReprValue_repr___closed__2 = (const lean_object*)&lp_SystemOSIOTLean_instReprValue_repr___closed__2_value;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprValue_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprValue_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_SystemOSIOTLean_instReprValue___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SystemOSIOTLean_instReprValue_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SystemOSIOTLean_instReprValue___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instReprValue___closed__0_value;
LEAN_EXPORT const lean_object* lp_SystemOSIOTLean_instReprValue = (const lean_object*)&lp_SystemOSIOTLean_instReprValue___closed__0_value;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Ty_toCtorIdx(lean_object*);
static const lean_string_object lp_SystemOSIOTLean_instReprTy_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Ty.nat"};
static const lean_object* lp_SystemOSIOTLean_instReprTy_repr___redArg___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instReprTy_repr___redArg___closed__0_value;
static const lean_ctor_object lp_SystemOSIOTLean_instReprTy_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_SystemOSIOTLean_instReprTy_repr___redArg___closed__0_value)}};
static const lean_object* lp_SystemOSIOTLean_instReprTy_repr___redArg___closed__1 = (const lean_object*)&lp_SystemOSIOTLean_instReprTy_repr___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprTy_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprTy_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprTy_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprTy_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_SystemOSIOTLean_instReprTy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SystemOSIOTLean_instReprTy_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SystemOSIOTLean_instReprTy___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instReprTy___closed__0_value;
LEAN_EXPORT const lean_object* lp_SystemOSIOTLean_instReprTy = (const lean_object*)&lp_SystemOSIOTLean_instReprTy___closed__0_value;
LEAN_EXPORT uint8_t lp_SystemOSIOTLean_instBEqTy_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instBEqTy_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_SystemOSIOTLean_instBEqTy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_SystemOSIOTLean_instBEqTy_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_SystemOSIOTLean_instBEqTy___closed__0 = (const lean_object*)&lp_SystemOSIOTLean_instBEqTy___closed__0_value;
LEAN_EXPORT const lean_object* lp_SystemOSIOTLean_instBEqTy = (const lean_object*)&lp_SystemOSIOTLean_instBEqTy___closed__0_value;
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_SystemOSIOTLean_Expr_ctorIdx(v_x_5_);
lean_dec_ref(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
switch(lean_obj_tag(v_t_7_))
{
case 0:
{
lean_object* v_a_9_; lean_object* v___x_10_; 
v_a_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_a_9_);
lean_dec_ref_known(v_t_7_, 1);
v___x_10_ = lean_apply_1(v_k_8_, v_a_9_);
return v___x_10_;
}
case 1:
{
lean_object* v_a_11_; lean_object* v_a_12_; lean_object* v___x_13_; 
v_a_11_ = lean_ctor_get(v_t_7_, 0);
lean_inc_ref(v_a_11_);
v_a_12_ = lean_ctor_get(v_t_7_, 1);
lean_inc_ref(v_a_12_);
lean_dec_ref_known(v_t_7_, 2);
v___x_13_ = lean_apply_2(v_k_8_, v_a_11_, v_a_12_);
return v___x_13_;
}
default: 
{
lean_object* v_a_14_; lean_object* v_a_15_; lean_object* v_a_16_; lean_object* v___x_17_; 
v_a_14_ = lean_ctor_get(v_t_7_, 0);
lean_inc_ref(v_a_14_);
v_a_15_ = lean_ctor_get(v_t_7_, 1);
lean_inc_ref(v_a_15_);
v_a_16_ = lean_ctor_get(v_t_7_, 2);
lean_inc_ref(v_a_16_);
lean_dec_ref_known(v_t_7_, 3);
v___x_17_ = lean_apply_3(v_k_8_, v_a_14_, v_a_15_, v_a_16_);
return v___x_17_;
}
}
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ctorElim(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lp_SystemOSIOTLean_Expr_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ctorElim___boxed(lean_object* v_motive_24_, lean_object* v_ctorIdx_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_k_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = lp_SystemOSIOTLean_Expr_ctorElim(v_motive_24_, v_ctorIdx_25_, v_t_26_, v_h_27_, v_k_28_);
lean_dec(v_ctorIdx_25_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_num_elim___redArg(lean_object* v_t_30_, lean_object* v_num_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lp_SystemOSIOTLean_Expr_ctorElim___redArg(v_t_30_, v_num_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_num_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_num_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_SystemOSIOTLean_Expr_ctorElim___redArg(v_t_34_, v_num_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_add_elim___redArg(lean_object* v_t_38_, lean_object* v_add_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lp_SystemOSIOTLean_Expr_ctorElim___redArg(v_t_38_, v_add_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_add_elim(lean_object* v_motive_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_add_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lp_SystemOSIOTLean_Expr_ctorElim___redArg(v_t_42_, v_add_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ifz_elim___redArg(lean_object* v_t_46_, lean_object* v_ifz_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lp_SystemOSIOTLean_Expr_ctorElim___redArg(v_t_46_, v_ifz_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Expr_ifz_elim(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_ifz_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lp_SystemOSIOTLean_Expr_ctorElim___redArg(v_t_50_, v_ifz_52_);
return v___x_53_;
}
}
static lean_object* _init_lp_SystemOSIOTLean_instReprExpr_repr___closed__3(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(2u);
v___x_61_ = lean_nat_to_int(v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_lp_SystemOSIOTLean_instReprExpr_repr___closed__4(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_nat_to_int(v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprExpr_repr(lean_object* v_x_76_, lean_object* v_prec_77_){
_start:
{
switch(lean_obj_tag(v_x_76_))
{
case 0:
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_98_; 
v_a_78_ = lean_ctor_get(v_x_76_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_98_ == 0)
{
v___x_80_ = v_x_76_;
v_isShared_81_ = v_isSharedCheck_98_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v_x_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_98_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___y_83_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_94_ = lean_unsigned_to_nat(1024u);
v___x_95_ = lean_nat_dec_le(v___x_94_, v_prec_77_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&lp_SystemOSIOTLean_instReprExpr_repr___closed__3, &lp_SystemOSIOTLean_instReprExpr_repr___closed__3_once, _init_lp_SystemOSIOTLean_instReprExpr_repr___closed__3);
v___y_83_ = v___x_96_;
goto v___jp_82_;
}
else
{
lean_object* v___x_97_; 
v___x_97_ = lean_obj_once(&lp_SystemOSIOTLean_instReprExpr_repr___closed__4, &lp_SystemOSIOTLean_instReprExpr_repr___closed__4_once, _init_lp_SystemOSIOTLean_instReprExpr_repr___closed__4);
v___y_83_ = v___x_97_;
goto v___jp_82_;
}
v___jp_82_:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_84_ = ((lean_object*)(lp_SystemOSIOTLean_instReprExpr_repr___closed__2));
v___x_85_ = l_Nat_reprFast(v_a_78_);
if (v_isShared_81_ == 0)
{
lean_ctor_set_tag(v___x_80_, 3);
lean_ctor_set(v___x_80_, 0, v___x_85_);
v___x_87_ = v___x_80_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v___x_85_);
v___x_87_ = v_reuseFailAlloc_93_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_84_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
lean_inc(v___y_83_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___y_83_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = l_Repr_addAppParen(v___x_91_, v_prec_77_);
return v___x_92_;
}
}
}
}
case 1:
{
lean_object* v_a_99_; lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_123_; 
v_a_99_ = lean_ctor_get(v_x_76_, 0);
v_a_100_ = lean_ctor_get(v_x_76_, 1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_x_76_);
if (v_isSharedCheck_123_ == 0)
{
v___x_102_ = v_x_76_;
v_isShared_103_ = v_isSharedCheck_123_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_inc(v_a_99_);
lean_dec(v_x_76_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_123_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___x_104_; lean_object* v___y_106_; uint8_t v___x_120_; 
v___x_104_ = lean_unsigned_to_nat(1024u);
v___x_120_ = lean_nat_dec_le(v___x_104_, v_prec_77_);
if (v___x_120_ == 0)
{
lean_object* v___x_121_; 
v___x_121_ = lean_obj_once(&lp_SystemOSIOTLean_instReprExpr_repr___closed__3, &lp_SystemOSIOTLean_instReprExpr_repr___closed__3_once, _init_lp_SystemOSIOTLean_instReprExpr_repr___closed__3);
v___y_106_ = v___x_121_;
goto v___jp_105_;
}
else
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&lp_SystemOSIOTLean_instReprExpr_repr___closed__4, &lp_SystemOSIOTLean_instReprExpr_repr___closed__4_once, _init_lp_SystemOSIOTLean_instReprExpr_repr___closed__4);
v___y_106_ = v___x_122_;
goto v___jp_105_;
}
v___jp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_107_ = lean_box(1);
v___x_108_ = ((lean_object*)(lp_SystemOSIOTLean_instReprExpr_repr___closed__7));
v___x_109_ = lp_SystemOSIOTLean_instReprExpr_repr(v_a_99_, v___x_104_);
if (v_isShared_103_ == 0)
{
lean_ctor_set_tag(v___x_102_, 5);
lean_ctor_set(v___x_102_, 1, v___x_109_);
lean_ctor_set(v___x_102_, 0, v___x_108_);
v___x_111_ = v___x_102_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___x_109_);
v___x_111_ = v_reuseFailAlloc_119_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_112_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v___x_107_);
v___x_113_ = lp_SystemOSIOTLean_instReprExpr_repr(v_a_100_, v___x_104_);
v___x_114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_112_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
lean_inc(v___y_106_);
v___x_115_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_115_, 0, v___y_106_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = 0;
v___x_117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_116_);
v___x_118_ = l_Repr_addAppParen(v___x_117_, v_prec_77_);
return v___x_118_;
}
}
}
}
default: 
{
lean_object* v_a_124_; lean_object* v_a_125_; lean_object* v_a_126_; lean_object* v___x_127_; lean_object* v___y_129_; uint8_t v___x_144_; 
v_a_124_ = lean_ctor_get(v_x_76_, 0);
lean_inc_ref(v_a_124_);
v_a_125_ = lean_ctor_get(v_x_76_, 1);
lean_inc_ref(v_a_125_);
v_a_126_ = lean_ctor_get(v_x_76_, 2);
lean_inc_ref(v_a_126_);
lean_dec_ref_known(v_x_76_, 3);
v___x_127_ = lean_unsigned_to_nat(1024u);
v___x_144_ = lean_nat_dec_le(v___x_127_, v_prec_77_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; 
v___x_145_ = lean_obj_once(&lp_SystemOSIOTLean_instReprExpr_repr___closed__3, &lp_SystemOSIOTLean_instReprExpr_repr___closed__3_once, _init_lp_SystemOSIOTLean_instReprExpr_repr___closed__3);
v___y_129_ = v___x_145_;
goto v___jp_128_;
}
else
{
lean_object* v___x_146_; 
v___x_146_ = lean_obj_once(&lp_SystemOSIOTLean_instReprExpr_repr___closed__4, &lp_SystemOSIOTLean_instReprExpr_repr___closed__4_once, _init_lp_SystemOSIOTLean_instReprExpr_repr___closed__4);
v___y_129_ = v___x_146_;
goto v___jp_128_;
}
v___jp_128_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_130_ = lean_box(1);
v___x_131_ = ((lean_object*)(lp_SystemOSIOTLean_instReprExpr_repr___closed__10));
v___x_132_ = lp_SystemOSIOTLean_instReprExpr_repr(v_a_124_, v___x_127_);
v___x_133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_131_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_130_);
v___x_135_ = lp_SystemOSIOTLean_instReprExpr_repr(v_a_125_, v___x_127_);
v___x_136_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v___x_130_);
v___x_138_ = lp_SystemOSIOTLean_instReprExpr_repr(v_a_126_, v___x_127_);
v___x_139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_137_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
lean_inc(v___y_129_);
v___x_140_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_140_, 0, v___y_129_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = 0;
v___x_142_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set_uint8(v___x_142_, sizeof(void*)*1, v___x_141_);
v___x_143_ = l_Repr_addAppParen(v___x_142_, v_prec_77_);
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprExpr_repr___boxed(lean_object* v_x_147_, lean_object* v_prec_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = lp_SystemOSIOTLean_instReprExpr_repr(v_x_147_, v_prec_148_);
lean_dec(v_prec_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprValue_repr(lean_object* v_x_158_, lean_object* v_prec_159_){
_start:
{
lean_object* v___y_161_; lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = lean_unsigned_to_nat(1024u);
v___x_171_ = lean_nat_dec_le(v___x_170_, v_prec_159_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; 
v___x_172_ = lean_obj_once(&lp_SystemOSIOTLean_instReprExpr_repr___closed__3, &lp_SystemOSIOTLean_instReprExpr_repr___closed__3_once, _init_lp_SystemOSIOTLean_instReprExpr_repr___closed__3);
v___y_161_ = v___x_172_;
goto v___jp_160_;
}
else
{
lean_object* v___x_173_; 
v___x_173_ = lean_obj_once(&lp_SystemOSIOTLean_instReprExpr_repr___closed__4, &lp_SystemOSIOTLean_instReprExpr_repr___closed__4_once, _init_lp_SystemOSIOTLean_instReprExpr_repr___closed__4);
v___y_161_ = v___x_173_;
goto v___jp_160_;
}
v___jp_160_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_162_ = ((lean_object*)(lp_SystemOSIOTLean_instReprValue_repr___closed__2));
v___x_163_ = l_Nat_reprFast(v_x_158_);
v___x_164_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
v___x_165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_162_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
lean_inc(v___y_161_);
v___x_166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_166_, 0, v___y_161_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = 0;
v___x_168_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*1, v___x_167_);
v___x_169_ = l_Repr_addAppParen(v___x_168_, v_prec_159_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprValue_repr___boxed(lean_object* v_x_174_, lean_object* v_prec_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = lp_SystemOSIOTLean_instReprValue_repr(v_x_174_, v_prec_175_);
lean_dec(v_prec_175_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_Ty_toCtorIdx(lean_object* v_x_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_unsigned_to_nat(0u);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprTy_repr___redArg(lean_object* v_prec_184_){
_start:
{
lean_object* v___y_186_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_192_ = lean_unsigned_to_nat(1024u);
v___x_193_ = lean_nat_dec_le(v___x_192_, v_prec_184_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
v___x_194_ = lean_obj_once(&lp_SystemOSIOTLean_instReprExpr_repr___closed__3, &lp_SystemOSIOTLean_instReprExpr_repr___closed__3_once, _init_lp_SystemOSIOTLean_instReprExpr_repr___closed__3);
v___y_186_ = v___x_194_;
goto v___jp_185_;
}
else
{
lean_object* v___x_195_; 
v___x_195_ = lean_obj_once(&lp_SystemOSIOTLean_instReprExpr_repr___closed__4, &lp_SystemOSIOTLean_instReprExpr_repr___closed__4_once, _init_lp_SystemOSIOTLean_instReprExpr_repr___closed__4);
v___y_186_ = v___x_195_;
goto v___jp_185_;
}
v___jp_185_:
{
lean_object* v___x_187_; lean_object* v___x_188_; uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_187_ = ((lean_object*)(lp_SystemOSIOTLean_instReprTy_repr___redArg___closed__1));
lean_inc(v___y_186_);
v___x_188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_188_, 0, v___y_186_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = 0;
v___x_190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_189_);
v___x_191_ = l_Repr_addAppParen(v___x_190_, v_prec_184_);
return v___x_191_;
}
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprTy_repr___redArg___boxed(lean_object* v_prec_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = lp_SystemOSIOTLean_instReprTy_repr___redArg(v_prec_196_);
lean_dec(v_prec_196_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprTy_repr(lean_object* v_x_198_, lean_object* v_prec_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lp_SystemOSIOTLean_instReprTy_repr___redArg(v_prec_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instReprTy_repr___boxed(lean_object* v_x_201_, lean_object* v_prec_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = lp_SystemOSIOTLean_instReprTy_repr(v_x_201_, v_prec_202_);
lean_dec(v_prec_202_);
return v_res_203_;
}
}
LEAN_EXPORT uint8_t lp_SystemOSIOTLean_instBEqTy_beq(lean_object* v_x_206_, lean_object* v_y_207_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = 1;
return v___x_208_;
}
}
LEAN_EXPORT lean_object* lp_SystemOSIOTLean_instBEqTy_beq___boxed(lean_object* v_x_209_, lean_object* v_y_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = lp_SystemOSIOTLean_instBEqTy_beq(v_x_209_, v_y_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_SystemOSIOTLean_SimpleTypeTheory(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
