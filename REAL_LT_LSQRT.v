Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_LSQRT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import POW_2_SQRT_spec.
Require Import REAL_POW_LE_spec.
Require Import SQRT_MONO_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1961043 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1961044 : term1 = term2.
Proof. exact (@lem1961043 term1). Qed.
Lemma lem1961045 : term2 = term1.
Proof. exact (SYM (@lem1961044)). Qed.
Lemma lem1961046 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1961049 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1961050 : term5.
Proof. exact (fun h0 : term4 => @lem1961049 h0). Qed.
Lemma lem1961051 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1961052 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1961053 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1961051 h2 (@lem1961052 h1)). Qed.
Lemma lem1961054 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1961053 h1 h0). Qed.
Lemma lem1961055 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1961056 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1961054 h1 (@lem1961055 h2)). Qed.
Lemma lem1961057 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1961056 h0 h1). Qed.
Lemma lem1961058 : term7.
Proof. exact (fun h0 : term5 => @lem1961057 h0). Qed.
Lemma lem1961061 : term5.
Proof. exact (@lem1961058 (@lem1961050)). Qed.
Lemma lem1961097 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1961098 : term8 = term9.
Proof. exact (@lem1961097 term10). Qed.
Lemma lem1961109 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1961110 : term12 = term13.
Proof. exact (MK_COMB (@lem1961109) (@lem1961098)). Qed.
Lemma lem1961113 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1961114 : term15 = term16.
Proof. exact (MK_COMB (@lem1961113) (@lem1961110)). Qed.
Lemma lem1961117 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1961124 : term4 = term18.
Proof. exact (MK_COMB (@lem1961117) (@lem1961114)). Qed.
Lemma lem1961129 (x : real) (y : real) : (term19 x y) = (term19 x y).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem1961130 (x : real) : (term20 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1961129 x y)). Qed.
Lemma lem1961131 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961132 (x : real) : (term21 x) = (term21 x).
Proof. exact (MK_COMB (@lem1961131) (@lem1961130 x)). Qed.
Lemma lem1961133 : term22 = term22.
Proof. exact (fun_ext (fun x : real => @lem1961132 x)). Qed.
Lemma lem1961134 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961135 : term10 = term10.
Proof. exact (MK_COMB (@lem1961134) (@lem1961133)). Qed.
Lemma lem1961136 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1961137 : term9 = term9.
Proof. exact (MK_COMB (@lem1961136) (@lem1961135)). Qed.
Lemma lem1961142 (x : real) (n : nat) : (term23 x n) = (term23 x n).
Proof. exact (eq_refl (term23 x n)). Qed.
Lemma lem1961143 (x : real) : (term24 x) = (term24 x).
Proof. exact (fun_ext (fun n : nat => @lem1961142 x n)). Qed.
Lemma lem1961144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1961145 (x : real) : (term25 x) = (term25 x).
Proof. exact (MK_COMB (@lem1961144) (@lem1961143 x)). Qed.
Lemma lem1961146 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem1961145 x)). Qed.
Lemma lem1961147 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961148 : term27 = term27.
Proof. exact (MK_COMB (@lem1961147) (@lem1961146)). Qed.
Lemma lem1961149 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1961150 : term11 = term11.
Proof. exact (MK_COMB (@lem1961149) (@lem1961148)). Qed.
Lemma lem1961151 : term13 = term13.
Proof. exact (MK_COMB (@lem1961150) (@lem1961137)). Qed.
Lemma lem1961156 (x : real) : (term28 x) = (term28 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1961157 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1961156 x)). Qed.
Lemma lem1961158 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961159 : term30 = term30.
Proof. exact (MK_COMB (@lem1961158) (@lem1961157)). Qed.
Lemma lem1961160 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1961161 : term14 = term14.
Proof. exact (MK_COMB (@lem1961160) (@lem1961159)). Qed.
Lemma lem1961162 : term16 = term16.
Proof. exact (MK_COMB (@lem1961161) (@lem1961151)). Qed.
Lemma lem1961171 (x : real) (y : real) : (term31 x y) = (term31 x y).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1961172 (x : real) : (term32 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1961171 x y)). Qed.
Lemma lem1961173 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961174 (x : real) : (term33 x) = (term33 x).
Proof. exact (MK_COMB (@lem1961173) (@lem1961172 x)). Qed.
Lemma lem1961175 : term34 = term34.
Proof. exact (fun_ext (fun x : real => @lem1961174 x)). Qed.
Lemma lem1961176 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961177 : term1 = term1.
Proof. exact (MK_COMB (@lem1961176) (@lem1961175)). Qed.
Lemma lem1961178 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1961179 : term3 = term3.
Proof. exact (MK_COMB (@lem1961178) (@lem1961177)). Qed.
Lemma lem1961180 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1961181 : term17 = term17.
Proof. exact (MK_COMB (@lem1961180) (@lem1961179)). Qed.
Lemma lem1961182 : term18 = term18.
Proof. exact (MK_COMB (@lem1961181) (@lem1961162)). Qed.
Lemma lem1961243 : term4 = term18.
Proof. exact (TRANS (@lem1961124) (@lem1961182)). Qed.
Lemma lem1961244 : term18 = term4.
Proof. exact (SYM (@lem1961243)). Qed.
Lemma lem1961245 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1961246 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem1961248 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1961259 (x : real) (y : real) : (term35 x y) = (term36 x y).
Proof. exact (@lem17362 (term37 x y) (term38 x y)). Qed.
Lemma lem1961260 (P : real -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1961261 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1961260 (term32 x)). Qed.
Lemma lem1961262 (x : real) (y : real) : (term43 x y) = (term31 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1961263 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1961264 (x : real) (y : real) : (term44 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1961263) (@lem1961262 x y)). Qed.
Lemma lem1961265 (x : real) (y : real) : (term44 x y) = (term36 x y).
Proof. exact (TRANS (@lem1961264 x y) (@lem1961259 x y)). Qed.
Lemma lem1961266 (x : real) : (term45 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1961265 x y)). Qed.
Lemma lem1961267 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1961268 (x : real) : (term42 x) = (term47 x).
Proof. exact (MK_COMB (@lem1961267) (@lem1961266 x)). Qed.
Lemma lem1961269 (x : real) : (term41 x) = (term47 x).
Proof. exact (TRANS (@lem1961261 x) (@lem1961268 x)). Qed.
Lemma lem1961270 (P : real -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1961271 : term3 = term48.
Proof. exact (@lem1961270 term34). Qed.
Lemma lem1961272 (x : real) : (term49 x) = (term33 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1961273 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1961274 (x : real) : (term50 x) = (term41 x).
Proof. exact (MK_COMB (@lem1961273) (@lem1961272 x)). Qed.
Lemma lem1961275 (x : real) : (term50 x) = (term47 x).
Proof. exact (TRANS (@lem1961274 x) (@lem1961269 x)). Qed.
Lemma lem1961276 : term51 = term52.
Proof. exact (fun_ext (fun x : real => @lem1961275 x)). Qed.
Lemma lem1961277 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1961278 : term48 = term53.
Proof. exact (MK_COMB (@lem1961277) (@lem1961276)). Qed.
Lemma lem1961335 : term3 = term53.
Proof. exact (TRANS (@lem1961271) (@lem1961278)). Qed.
Lemma lem1961336 (h1 : term3) : term53.
Proof. exact (EQ_MP (@lem1961335) (@lem1961245 h1)). Qed.
Lemma lem1961343 (x : real) : (term28 x) = (term54 x).
Proof. exact (@lem17265 (term55 x) ((term56 x) = x)). Qed.
Lemma lem1961344 : term29 = term57.
Proof. exact (fun_ext (fun x : real => @lem1961343 x)). Qed.
Lemma lem1961345 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961398 : term30 = term58.
Proof. exact (MK_COMB (@lem1961345) (@lem1961344)). Qed.
Lemma lem1961399 (h1 : term30) : term58.
Proof. exact (EQ_MP (@lem1961398) (@lem1961246 h1)). Qed.
Lemma lem1961502 (x : real) (y : real) : (term19 x y) = (term59 x y).
Proof. exact (@lem17265 (real_lt x y) (term60 x y)). Qed.
Lemma lem1961503 (x : real) : (term20 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1961502 x y)). Qed.
Lemma lem1961504 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961505 (x : real) : (term21 x) = (term62 x).
Proof. exact (MK_COMB (@lem1961504) (@lem1961503 x)). Qed.
Lemma lem1961506 : term22 = term63.
Proof. exact (fun_ext (fun x : real => @lem1961505 x)). Qed.
Lemma lem1961507 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961564 : term10 = term64.
Proof. exact (MK_COMB (@lem1961507) (@lem1961506)). Qed.
Lemma lem1961565 (h1 : term10) : term64.
Proof. exact (EQ_MP (@lem1961564) (@lem1961248 h1)). Qed.
Lemma lem1961566 (x : real) (h1 : term47 x) : term47 x.
Proof. exact (h1). Qed.
Lemma lem1961598 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1961599 : term57 = term57.
Proof. exact (fun_ext (fun x : real => @lem1961598 x)). Qed.
Lemma lem1961600 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961601 : term58 = term58.
Proof. exact (MK_COMB (@lem1961600) (@lem1961599)). Qed.
Lemma lem1961602 (h1 : term30) : term58.
Proof. exact (EQ_MP (@lem1961601) (@lem1961399 h1)). Qed.
Lemma lem1961655 (x : real) (y : real) : (term59 x y) = (term59 x y).
Proof. exact (eq_refl (term59 x y)). Qed.
Lemma lem1961656 (x : real) : (term61 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1961655 x y)). Qed.
Lemma lem1961657 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961658 (x : real) : (term62 x) = (term62 x).
Proof. exact (MK_COMB (@lem1961657) (@lem1961656 x)). Qed.
Lemma lem1961659 : term63 = term63.
Proof. exact (fun_ext (fun x : real => @lem1961658 x)). Qed.
Lemma lem1961660 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961661 : term64 = term64.
Proof. exact (MK_COMB (@lem1961660) (@lem1961659)). Qed.
Lemma lem1961662 (h1 : term10) : term64.
Proof. exact (EQ_MP (@lem1961661) (@lem1961565 h1)). Qed.
Lemma lem1961702 (x : real) (y : real) (h1 : term36 x y) : term36 x y.
Proof. exact (h1). Qed.
Lemma lem1961704 (x : real) (y : real) (h1 : term36 x y) : term37 x y.
Proof. exact (proj1 (@lem1961702 x y h1)). Qed.
Lemma lem1961714 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1961715 : term57 = term57.
Proof. exact (fun_ext (fun x : real => @lem1961714 x)). Qed.
Lemma lem1961716 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961718 : term58 = term58.
Proof. exact (MK_COMB (@lem1961716) (@lem1961715)). Qed.
Lemma lem1961719 (h1 : term30) : term58.
Proof. exact (EQ_MP (@lem1961718) (@lem1961602 h1)). Qed.
Lemma lem1961765 (x : real) (y : real) : (term59 x y) = (term59 x y).
Proof. exact (eq_refl (term59 x y)). Qed.
Lemma lem1961766 (x : real) : (term61 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1961765 x y)). Qed.
Lemma lem1961767 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961768 (x : real) : (term62 x) = (term62 x).
Proof. exact (MK_COMB (@lem1961767) (@lem1961766 x)). Qed.
Lemma lem1961769 : term63 = term63.
Proof. exact (fun_ext (fun x : real => @lem1961768 x)). Qed.
Lemma lem1961770 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1961772 : term64 = term64.
Proof. exact (MK_COMB (@lem1961770) (@lem1961769)). Qed.
Lemma lem1961773 (h1 : term10) : term64.
Proof. exact (EQ_MP (@lem1961772) (@lem1961662 h1)). Qed.
Lemma lem1961786 (_27537 : real) (h1 : term30) : term65 _27537.
Proof. exact (@lem1961719 h1 _27537). Qed.
Lemma lem1961787 (_27537 : real) : (term65 _27537) = (term54 _27537).
Proof. exact (eq_refl (term65 _27537)). Qed.
Lemma lem1961795 (_27540 : real) (h1 : term10) : term66 _27540.
Proof. exact (@lem1961773 h1 _27540). Qed.
Lemma lem1961796 (_27540 : real) : (term66 _27540) = (term62 _27540).
Proof. exact (eq_refl (term66 _27540)). Qed.
Lemma lem1961797 (_27540 : real) (h1 : term10) : term62 _27540.
Proof. exact (EQ_MP (@lem1961796 _27540) (@lem1961795 _27540 h1)). Qed.
Lemma lem1961798 (_27540 : real) (_27541 : real) (h1 : term10) : term67 _27540 _27541.
Proof. exact (@lem1961797 _27540 h1 _27541). Qed.
Lemma lem1961799 (_27540 : real) (_27541 : real) : (term67 _27540 _27541) = (term59 _27540 _27541).
Proof. exact (eq_refl (term67 _27540 _27541)). Qed.
Lemma lem1961806 (_27537 : real) (h1 : term30) : term54 _27537.
Proof. exact (EQ_MP (@lem1961787 _27537) (@lem1961786 _27537 h1)). Qed.
Lemma lem1961818 (_27540 : real) (_27541 : real) (h1 : term10) : term59 _27540 _27541.
Proof. exact (EQ_MP (@lem1961799 _27540 _27541) (@lem1961798 _27540 _27541 h1)). Qed.
Lemma lem1961820 (x : real) (y : real) (h1 : term36 x y) : term68 x y.
Proof. exact (proj2 (@lem1961702 x y h1)). Qed.
Lemma lem1961825 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1961826 (_27542 : real) (_27544 : real) (h1 : _27542 = _27544) : _27542 = _27544.
Proof. exact (h1). Qed.
Lemma lem1961827 (_27543 : real) (_27545 : real) (h1 : _27543 = _27545) : _27543 = _27545.
Proof. exact (h1). Qed.
Lemma lem1961828 (_27542 : real) (_27544 : real) (h1 : _27542 = _27544) : (real_lt _27542) = (real_lt _27544).
Proof. exact (MK_COMB (@lem1961825) (@lem1961826 _27542 _27544 h1)). Qed.
Lemma lem1961829 (_27542 : real) (_27544 : real) (_27543 : real) (_27545 : real) (h1 : _27542 = _27544) (h2 : _27543 = _27545) : (real_lt _27542 _27543) = (real_lt _27544 _27545).
Proof. exact (MK_COMB (@lem1961828 _27542 _27544 h1) (@lem1961827 _27543 _27545 h2)). Qed.
Lemma lem1961831 (b : Prop) (a : Prop) : term69 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1961832 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : term70 _27544 _27545 _27542 _27543.
Proof. exact (@lem1961831 (real_lt _27544 _27545) (real_lt _27542 _27543)). Qed.
Lemma lem1961833 (_27542 : real) (_27544 : real) (_27543 : real) (_27545 : real) (h1 : _27542 = _27544) (h2 : _27543 = _27545) : term71 _27544 _27545 _27542 _27543.
Proof. exact (@lem1961832 _27544 _27545 _27542 _27543 (@lem1961829 _27542 _27544 _27543 _27545 h1 h2)). Qed.
Lemma lem1961834 (_27545 : real) (_27543 : real) (_27542 : real) (_27544 : real) (h1 : _27542 = _27544) : term72 _27544 _27545 _27542 _27543.
Proof. exact (fun h0 : _27543 = _27545 => @lem1961833 _27542 _27544 _27543 _27545 h1 h0). Qed.
Lemma lem1961836 (a : Prop) (b : Prop) : (a -> b) = (term73 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1961837 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : (term72 _27544 _27545 _27542 _27543) = (term74 _27544 _27545 _27542 _27543).
Proof. exact (@lem1961836 (_27543 = _27545) (term71 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1961838 (_27545 : real) (_27543 : real) (_27542 : real) (_27544 : real) (h1 : _27542 = _27544) : term74 _27544 _27545 _27542 _27543.
Proof. exact (EQ_MP (@lem1961837 _27544 _27545 _27542 _27543) (@lem1961834 _27545 _27543 _27542 _27544 h1)). Qed.
Lemma lem1961839 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : term75 _27544 _27545 _27542 _27543.
Proof. exact (fun h0 : _27542 = _27544 => @lem1961838 _27545 _27543 _27542 _27544 h0). Qed.
Lemma lem1961841 (a : Prop) (b : Prop) : (a -> b) = (term73 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1961842 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : (term75 _27544 _27545 _27542 _27543) = (term76 _27544 _27545 _27542 _27543).
Proof. exact (@lem1961841 (_27542 = _27544) (term74 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1961843 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : term76 _27544 _27545 _27542 _27543.
Proof. exact (EQ_MP (@lem1961842 _27544 _27545 _27542 _27543) (@lem1961839 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1961923 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1961924 (x : real) : (sqrt x) = (sqrt x).
Proof. exact (@lem1961923 (sqrt x)). Qed.
Lemma lem1961925 (x : real) : term77 x.
Proof. exact (fun h0 : term78 x => @lem1961924 x). Qed.
Lemma lem1961927 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1961928 (x : real) : (term77 x) = ((sqrt x) = (sqrt x)).
Proof. exact (@lem1961927 ((sqrt x) = (sqrt x))). Qed.
Lemma lem1961929 (x : real) : (sqrt x) = (sqrt x).
Proof. exact (EQ_MP (@lem1961928 x) (@lem1961925 x)). Qed.
Lemma lem1961931 (x : real) (y : real) (h1 : term36 x y) : term55 y.
Proof. exact (proj1 (@lem1961704 x y h1)). Qed.
Lemma lem1961932 (x : real) (y : real) (h1 : term36 x y) : term80 y.
Proof. exact (fun h0 : term81 y => @lem1961931 x y h1). Qed.
Lemma lem1961934 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1961935 (y : real) : (term80 y) = (term55 y).
Proof. exact (@lem1961934 (term55 y)). Qed.
Lemma lem1961936 (x : real) (y : real) (h1 : term36 x y) : term55 y.
Proof. exact (EQ_MP (@lem1961935 y) (@lem1961932 x y h1)). Qed.
Lemma lem1961942 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1961943 (_27537 : real) : (term54 _27537) = (term82 _27537).
Proof. exact (@lem1961942 ((term56 _27537) = _27537) (term81 _27537)). Qed.
Lemma lem1961951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1961952 (_27537 : real) : (term83 _27537) = (term84 _27537).
Proof. exact (MK_COMB (@lem1961951) (@lem1961943 _27537)). Qed.
Lemma lem1961960 (_27537 : real) : (term82 _27537) = (term82 _27537).
Proof. exact (eq_refl (term82 _27537)). Qed.
Lemma lem1961961 (_27537 : real) : ((term54 _27537) = (term82 _27537)) = ((term82 _27537) = (term82 _27537)).
Proof. exact (MK_COMB (@lem1961952 _27537) (@lem1961960 _27537)). Qed.
Lemma lem1961963 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1961964 (x : Prop) : (x = x) = True.
Proof. exact (@lem1961963 Prop x). Qed.
Lemma lem1961965 (_27537 : real) : ((term82 _27537) = (term82 _27537)) = True.
Proof. exact (@lem1961964 (term82 _27537)). Qed.
Lemma lem1961966 (_27537 : real) : ((term54 _27537) = (term82 _27537)) = True.
Proof. exact (TRANS (@lem1961961 _27537) (@lem1961965 _27537)). Qed.
Lemma lem1961967 (_27537 : real) : True = ((term54 _27537) = (term82 _27537)).
Proof. exact (SYM (@lem1961966 _27537)). Qed.
Lemma lem1961968 (_27537 : real) : (term54 _27537) = (term82 _27537).
Proof. exact (EQ_MP (@lem1961967 _27537) (@lem0)). Qed.
Lemma lem1961969 (_27537 : real) (h1 : term30) : term82 _27537.
Proof. exact (EQ_MP (@lem1961968 _27537) (@lem1961806 _27537 h1)). Qed.
Lemma lem1961971 (b : Prop) (a : Prop) : (a \/ b) = (term85 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1961972 (_27537 : real) : (term82 _27537) = (term86 _27537).
Proof. exact (@lem1961971 (term81 _27537) ((term56 _27537) = _27537)). Qed.
Lemma lem1961974 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1961975 (_27537 : real) : (term88 _27537) = (term55 _27537).
Proof. exact (@lem1961974 (term55 _27537)). Qed.
Lemma lem1961976 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1961977 (_27537 : real) : (term89 _27537) = (term90 _27537).
Proof. exact (MK_COMB (@lem1961976) (@lem1961975 _27537)). Qed.
Lemma lem1961978 (_27537 : real) : ((term56 _27537) = _27537) = ((term56 _27537) = _27537).
Proof. exact (eq_refl ((term56 _27537) = _27537)). Qed.
Lemma lem1961979 (_27537 : real) : (term86 _27537) = (term28 _27537).
Proof. exact (MK_COMB (@lem1961977 _27537) (@lem1961978 _27537)). Qed.
Lemma lem1961980 (_27537 : real) : (term82 _27537) = (term28 _27537).
Proof. exact (TRANS (@lem1961972 _27537) (@lem1961979 _27537)). Qed.
Lemma lem1961983 (_27537 : real) (h1 : term30) : term28 _27537.
Proof. exact (EQ_MP (@lem1961980 _27537) (@lem1961969 _27537 h1)). Qed.
Lemma lem1961984 (y : real) (h1 : term30) : term28 y.
Proof. exact (@lem1961983 y h1). Qed.
Lemma lem1961987 (x : real) (y : real) (h1 : term30) (h2 : term36 x y) : (term56 y) = y.
Proof. exact (@lem1961984 y h1 (@lem1961936 x y h2)). Qed.
Lemma lem1961988 (x : real) (y : real) (h1 : term30) (h2 : term36 x y) : term91 y.
Proof. exact (fun h0 : term92 y => @lem1961987 x y h1 h2). Qed.
Lemma lem1961990 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1961991 (y : real) : (term91 y) = ((term56 y) = y).
Proof. exact (@lem1961990 ((term56 y) = y)). Qed.
Lemma lem1961992 (x : real) (y : real) (h1 : term30) (h2 : term36 x y) : (term56 y) = y.
Proof. exact (EQ_MP (@lem1961991 y) (@lem1961988 x y h1 h2)). Qed.
Lemma lem1961994 (x : real) (y : real) (h1 : term36 x y) : term93 x y.
Proof. exact (proj2 (@lem1961704 x y h1)). Qed.
Lemma lem1961995 (x : real) (y : real) (h1 : term36 x y) : term94 x y.
Proof. exact (fun h0 : term95 x y => @lem1961994 x y h1). Qed.
Lemma lem1961997 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1961998 (x : real) (y : real) : (term94 x y) = (term93 x y).
Proof. exact (@lem1961997 (term93 x y)). Qed.
Lemma lem1961999 (x : real) (y : real) (h1 : term36 x y) : term93 x y.
Proof. exact (EQ_MP (@lem1961998 x y) (@lem1961995 x y h1)). Qed.
Lemma lem1962005 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1962006 (_27540 : real) (_27541 : real) : (term59 _27540 _27541) = (term96 _27540 _27541).
Proof. exact (@lem1962005 (term60 _27540 _27541) (term97 _27540 _27541)). Qed.
Lemma lem1962012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1962013 (_27540 : real) (_27541 : real) : (term98 _27540 _27541) = (term99 _27540 _27541).
Proof. exact (MK_COMB (@lem1962012) (@lem1962006 _27540 _27541)). Qed.
Lemma lem1962019 (_27540 : real) (_27541 : real) : (term96 _27540 _27541) = (term96 _27540 _27541).
Proof. exact (eq_refl (term96 _27540 _27541)). Qed.
Lemma lem1962020 (_27540 : real) (_27541 : real) : ((term59 _27540 _27541) = (term96 _27540 _27541)) = ((term96 _27540 _27541) = (term96 _27540 _27541)).
Proof. exact (MK_COMB (@lem1962013 _27540 _27541) (@lem1962019 _27540 _27541)). Qed.
Lemma lem1962022 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1962023 (x : Prop) : (x = x) = True.
Proof. exact (@lem1962022 Prop x). Qed.
Lemma lem1962024 (_27540 : real) (_27541 : real) : ((term96 _27540 _27541) = (term96 _27540 _27541)) = True.
Proof. exact (@lem1962023 (term96 _27540 _27541)). Qed.
Lemma lem1962025 (_27540 : real) (_27541 : real) : ((term59 _27540 _27541) = (term96 _27540 _27541)) = True.
Proof. exact (TRANS (@lem1962020 _27540 _27541) (@lem1962024 _27540 _27541)). Qed.
Lemma lem1962026 (_27540 : real) (_27541 : real) : True = ((term59 _27540 _27541) = (term96 _27540 _27541)).
Proof. exact (SYM (@lem1962025 _27540 _27541)). Qed.
Lemma lem1962027 (_27540 : real) (_27541 : real) : (term59 _27540 _27541) = (term96 _27540 _27541).
Proof. exact (EQ_MP (@lem1962026 _27540 _27541) (@lem0)). Qed.
Lemma lem1962028 (_27540 : real) (_27541 : real) (h1 : term10) : term96 _27540 _27541.
Proof. exact (EQ_MP (@lem1962027 _27540 _27541) (@lem1961818 _27540 _27541 h1)). Qed.
Lemma lem1962030 (b : Prop) (a : Prop) : (a \/ b) = (term85 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1962031 (_27540 : real) (_27541 : real) : (term96 _27540 _27541) = (term100 _27540 _27541).
Proof. exact (@lem1962030 (term97 _27540 _27541) (term60 _27540 _27541)). Qed.
Lemma lem1962033 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1962034 (_27540 : real) (_27541 : real) : (term101 _27540 _27541) = (real_lt _27540 _27541).
Proof. exact (@lem1962033 (real_lt _27540 _27541)). Qed.
Lemma lem1962035 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1962036 (_27540 : real) (_27541 : real) : (term102 _27540 _27541) = (term103 _27540 _27541).
Proof. exact (MK_COMB (@lem1962035) (@lem1962034 _27540 _27541)). Qed.
Lemma lem1962037 (_27540 : real) (_27541 : real) : (term60 _27540 _27541) = (term60 _27540 _27541).
Proof. exact (eq_refl (term60 _27540 _27541)). Qed.
Lemma lem1962038 (_27540 : real) (_27541 : real) : (term100 _27540 _27541) = (term19 _27540 _27541).
Proof. exact (MK_COMB (@lem1962036 _27540 _27541) (@lem1962037 _27540 _27541)). Qed.
Lemma lem1962039 (_27540 : real) (_27541 : real) : (term96 _27540 _27541) = (term19 _27540 _27541).
Proof. exact (TRANS (@lem1962031 _27540 _27541) (@lem1962038 _27540 _27541)). Qed.
Lemma lem1962042 (_27540 : real) (_27541 : real) (h1 : term10) : term19 _27540 _27541.
Proof. exact (EQ_MP (@lem1962039 _27540 _27541) (@lem1962028 _27540 _27541 h1)). Qed.
Lemma lem1962043 (x : real) (y : real) (h1 : term10) : term104 x y.
Proof. exact (@lem1962042 x (term105 y) h1). Qed.
Lemma lem1962046 (x : real) (y : real) (h1 : term10) (h2 : term36 x y) : term106 x y.
Proof. exact (@lem1962043 x y h1 (@lem1961999 x y h2)). Qed.
Lemma lem1962047 (x : real) (y : real) (h1 : term10) (h2 : term36 x y) : term107 x y.
Proof. exact (fun h0 : term108 x y => @lem1962046 x y h1 h2). Qed.
Lemma lem1962049 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1962050 (x : real) (y : real) : (term107 x y) = (term106 x y).
Proof. exact (@lem1962049 (term106 x y)). Qed.
Lemma lem1962051 (x : real) (y : real) (h1 : term10) (h2 : term36 x y) : term106 x y.
Proof. exact (EQ_MP (@lem1962050 x y) (@lem1962047 x y h1 h2)). Qed.
Lemma lem1962069 (q : Prop) (p : Prop) (r : Prop) : (term109 p q r) = (term109 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1962070 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : (term74 _27544 _27545 _27542 _27543) = (term110 _27544 _27545 _27542 _27543).
Proof. exact (@lem1962069 (real_lt _27544 _27545) (term111 _27543 _27545) (term97 _27542 _27543)). Qed.
Lemma lem1962088 (_27542 : real) (_27544 : real) : (term112 _27542 _27544) = (term112 _27542 _27544).
Proof. exact (eq_refl (term112 _27542 _27544)). Qed.
Lemma lem1962089 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : (term76 _27544 _27545 _27542 _27543) = (term113 _27544 _27545 _27542 _27543).
Proof. exact (MK_COMB (@lem1962088 _27542 _27544) (@lem1962070 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1962093 (q : Prop) (p : Prop) (r : Prop) : (term109 p q r) = (term109 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1962094 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : (term113 _27544 _27545 _27542 _27543) = (term114 _27544 _27545 _27542 _27543).
Proof. exact (@lem1962093 (real_lt _27544 _27545) (term111 _27542 _27544) (term115 _27545 _27542 _27543)). Qed.
Lemma lem1962124 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : (term76 _27544 _27545 _27542 _27543) = (term114 _27544 _27545 _27542 _27543).
Proof. exact (TRANS (@lem1962089 _27544 _27545 _27542 _27543) (@lem1962094 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1962125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1962126 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : (term116 _27544 _27545 _27542 _27543) = (term117 _27544 _27545 _27542 _27543).
Proof. exact (MK_COMB (@lem1962125) (@lem1962124 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1962156 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : (term114 _27544 _27545 _27542 _27543) = (term114 _27544 _27545 _27542 _27543).
Proof. exact (eq_refl (term114 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1962157 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : ((term76 _27544 _27545 _27542 _27543) = (term114 _27544 _27545 _27542 _27543)) = ((term114 _27544 _27545 _27542 _27543) = (term114 _27544 _27545 _27542 _27543)).
Proof. exact (MK_COMB (@lem1962126 _27544 _27545 _27542 _27543) (@lem1962156 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1962159 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1962160 (x : Prop) : (x = x) = True.
Proof. exact (@lem1962159 Prop x). Qed.
Lemma lem1962161 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : ((term114 _27544 _27545 _27542 _27543) = (term114 _27544 _27545 _27542 _27543)) = True.
Proof. exact (@lem1962160 (term114 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1962162 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : ((term76 _27544 _27545 _27542 _27543) = (term114 _27544 _27545 _27542 _27543)) = True.
Proof. exact (TRANS (@lem1962157 _27544 _27545 _27542 _27543) (@lem1962161 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1962163 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : True = ((term76 _27544 _27545 _27542 _27543) = (term114 _27544 _27545 _27542 _27543)).
Proof. exact (SYM (@lem1962162 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1962164 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : (term76 _27544 _27545 _27542 _27543) = (term114 _27544 _27545 _27542 _27543).
Proof. exact (EQ_MP (@lem1962163 _27544 _27545 _27542 _27543) (@lem0)). Qed.
Lemma lem1962165 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : term114 _27544 _27545 _27542 _27543.
Proof. exact (EQ_MP (@lem1962164 _27544 _27545 _27542 _27543) (@lem1961843 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1962167 (b : Prop) (a : Prop) : (a \/ b) = (term85 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1962168 (_27542 : real) (_27543 : real) (_27544 : real) (_27545 : real) : (term114 _27544 _27545 _27542 _27543) = (term118 _27542 _27543 _27544 _27545).
Proof. exact (@lem1962167 (term119 _27544 _27545 _27542 _27543) (real_lt _27544 _27545)). Qed.
Lemma lem1962170 (a : Prop) (b : Prop) : (term120 a b) = (term121 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1962171 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : (term122 _27544 _27545 _27542 _27543) = (term123 _27544 _27545 _27542 _27543).
Proof. exact (@lem1962170 (term111 _27542 _27544) (term115 _27545 _27542 _27543)). Qed.
Lemma lem1962173 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1962174 (_27542 : real) (_27544 : real) : (term124 _27542 _27544) = (_27542 = _27544).
Proof. exact (@lem1962173 (_27542 = _27544)). Qed.
Lemma lem1962175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1962176 (_27542 : real) (_27544 : real) : (term125 _27542 _27544) = (term126 _27542 _27544).
Proof. exact (MK_COMB (@lem1962175) (@lem1962174 _27542 _27544)). Qed.
Lemma lem1962178 (a : Prop) (b : Prop) : (term120 a b) = (term121 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1962179 (_27545 : real) (_27542 : real) (_27543 : real) : (term127 _27545 _27542 _27543) = (term128 _27545 _27542 _27543).
Proof. exact (@lem1962178 (term111 _27543 _27545) (term97 _27542 _27543)). Qed.
Lemma lem1962181 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1962182 (_27543 : real) (_27545 : real) : (term124 _27543 _27545) = (_27543 = _27545).
Proof. exact (@lem1962181 (_27543 = _27545)). Qed.
Lemma lem1962183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1962184 (_27543 : real) (_27545 : real) : (term125 _27543 _27545) = (term126 _27543 _27545).
Proof. exact (MK_COMB (@lem1962183) (@lem1962182 _27543 _27545)). Qed.
Lemma lem1962186 (a : Prop) : (term87 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1962187 (_27542 : real) (_27543 : real) : (term101 _27542 _27543) = (real_lt _27542 _27543).
Proof. exact (@lem1962186 (real_lt _27542 _27543)). Qed.
Lemma lem1962188 (_27545 : real) (_27542 : real) (_27543 : real) : (term128 _27545 _27542 _27543) = (term129 _27545 _27542 _27543).
Proof. exact (MK_COMB (@lem1962184 _27543 _27545) (@lem1962187 _27542 _27543)). Qed.
Lemma lem1962189 (_27545 : real) (_27542 : real) (_27543 : real) : (term127 _27545 _27542 _27543) = (term129 _27545 _27542 _27543).
Proof. exact (TRANS (@lem1962179 _27545 _27542 _27543) (@lem1962188 _27545 _27542 _27543)). Qed.
Lemma lem1962190 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : (term123 _27544 _27545 _27542 _27543) = (term130 _27544 _27545 _27542 _27543).
Proof. exact (MK_COMB (@lem1962176 _27542 _27544) (@lem1962189 _27545 _27542 _27543)). Qed.
Lemma lem1962191 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : (term122 _27544 _27545 _27542 _27543) = (term130 _27544 _27545 _27542 _27543).
Proof. exact (TRANS (@lem1962171 _27544 _27545 _27542 _27543) (@lem1962190 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1962192 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1962193 (_27544 : real) (_27545 : real) (_27542 : real) (_27543 : real) : (term131 _27544 _27545 _27542 _27543) = (term132 _27544 _27545 _27542 _27543).
Proof. exact (MK_COMB (@lem1962192) (@lem1962191 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1962194 (_27544 : real) (_27545 : real) : (real_lt _27544 _27545) = (real_lt _27544 _27545).
Proof. exact (eq_refl (real_lt _27544 _27545)). Qed.
Lemma lem1962195 (_27542 : real) (_27543 : real) (_27544 : real) (_27545 : real) : (term118 _27542 _27543 _27544 _27545) = (term133 _27542 _27543 _27544 _27545).
Proof. exact (MK_COMB (@lem1962193 _27544 _27545 _27542 _27543) (@lem1962194 _27544 _27545)). Qed.
Lemma lem1962196 (_27542 : real) (_27543 : real) (_27544 : real) (_27545 : real) : (term114 _27544 _27545 _27542 _27543) = (term133 _27542 _27543 _27544 _27545).
Proof. exact (TRANS (@lem1962168 _27542 _27543 _27544 _27545) (@lem1962195 _27542 _27543 _27544 _27545)). Qed.
Lemma lem1962198 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : term134 x y.
Proof. exact (conj (@lem1961992 x y h2 h3) (@lem1962051 x y h1 h3)). Qed.
Lemma lem1962199 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : term135 x y.
Proof. exact (conj (@lem1961929 x) (@lem1962198 x y h1 h2 h3)). Qed.
Lemma lem1962201 (_27542 : real) (_27543 : real) (_27544 : real) (_27545 : real) : term133 _27542 _27543 _27544 _27545.
Proof. exact (EQ_MP (@lem1962196 _27542 _27543 _27544 _27545) (@lem1962165 _27544 _27545 _27542 _27543)). Qed.
Lemma lem1962202 (x : real) (y : real) : term136 x y.
Proof. exact (@lem1962201 (sqrt x) (term56 y) (sqrt x) y). Qed.
Lemma lem1962205 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : term38 x y.
Proof. exact (@lem1962202 x y (@lem1962199 x y h1 h2 h3)). Qed.
Lemma lem1962206 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : term137 x y.
Proof. exact (fun h0 : term68 x y => @lem1962205 x y h1 h2 h3). Qed.
Lemma lem1962208 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1962209 (x : real) (y : real) : (term137 x y) = (term38 x y).
Proof. exact (@lem1962208 (term38 x y)). Qed.
Lemma lem1962210 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : term38 x y.
Proof. exact (EQ_MP (@lem1962209 x y) (@lem1962206 x y h1 h2 h3)). Qed.
Lemma lem1962213 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1962215 (x : real) (y : real) : (term68 x y) = (term138 x y).
Proof. exact (@lem1962213 (term38 x y)). Qed.
Lemma lem1962218 (x : real) (y : real) (h1 : term36 x y) : term138 x y.
Proof. exact (EQ_MP (@lem1962215 x y) (@lem1961820 x y h1)). Qed.
Lemma lem1962221 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : False.
Proof. exact (@lem1962218 x y h3 (@lem1962210 x y h1 h2 h3)). Qed.
Lemma lem1962222 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : term139.
Proof. exact (fun h0 : ~ False => @lem1962221 x y h1 h2 h3). Qed.
Lemma lem1962224 (p : Prop) : (term79 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1962225 : term139 = False.
Proof. exact (@lem1962224 False). Qed.
Lemma lem1962226 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : False.
Proof. exact (EQ_MP (@lem1962225) (@lem1962222 x y h1 h2 h3)). Qed.
Lemma lem1962227 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : (term36 x y) = False.
Proof. exact (prop_ext (fun h4 : term36 x y => @lem1962226 x y h1 h2 h3) (fun h4 : False => @lem1961702 x y h3)). Qed.
Lemma lem1962228 (x : real) (y : real) (h1 : term10) (h2 : term30) (h3 : term36 x y) : False.
Proof. exact (EQ_MP (@lem1962227 x y h1 h2 h3) (@lem1961702 x y h3)). Qed.
Lemma lem1962229 (x : real) (h1 : term10) (h2 : term30) (h3 : term47 x) : False.
Proof. exact (ex_elim (@lem1961566 x h3) (fun y : real => fun h0 : term46 x y => @lem1962228 x y h1 h2 h0)). Qed.
Lemma lem1962230 (h1 : term10) (h2 : term30) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1961336 h3) (fun x : real => fun h0 : term52 x => @lem1962229 x h1 h2 h0)). Qed.
Lemma lem1962231 (h1 : term30) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1962230 h0 h1 h2). Qed.
Lemma lem1962232 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1962233 (h1 : term30) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1962232) (@lem1962231 h1 h2)). Qed.
Lemma lem1962234 (h1 : term30) (h2 : term3) : term13.
Proof. exact (fun h0 : term27 => @lem1962233 h1 h2). Qed.
Lemma lem1962235 (h1 : term3) : term16.
Proof. exact (fun h0 : term30 => @lem1962234 h0 h1). Qed.
Lemma lem1962236 : term18.
Proof. exact (fun h0 : term3 => @lem1962235 h0). Qed.
Lemma lem1962237 : term4.
Proof. exact (EQ_MP (@lem1961244) (@lem1962236)). Qed.
Lemma lem1962239 : term4.
Proof. exact (@lem1961061 (@lem1962237)). Qed.
Lemma lem1962240 (h1 : term3) : term15.
Proof. exact (@lem1962239 (@lem1961046 h1)). Qed.
Lemma lem1962241 (h1 : term3) : term12.
Proof. exact (@lem1962240 h1 (@lem1900729)). Qed.
Lemma lem1962242 (h1 : term3) : term8.
Proof. exact (@lem1962241 h1 (@lem1582434)). Qed.
Lemma lem1962243 (h1 : term3) : False.
Proof. exact (@lem1962242 h1 (@lem1950431)). Qed.
Lemma lem1962244 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1962243 h1) (fun h2 : False => @lem1961046 h1)). Qed.
Lemma lem1962245 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1962244 h1) (@lem1961046 h1)). Qed.
Lemma lem1962246 : term2.
Proof. exact (fun h0 : term3 => @lem1962245 h0). Qed.
Lemma lem1962247 : term1.
Proof. exact (EQ_MP (@lem1961045) (@lem1962246)). Qed.
