Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_HREAL_LEMMA2_term_abbrevs.
Require Import EQ_SYM_EQ_spec.
Require Import EXISTS_REFL_spec.
Require Import REAL_HREAL_LEMMA1_spec.
Require Import SELECT_REFL_spec.
Require Import thm0_spec.
Require Import thm1319377_spec.
Require Import thm1339379_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm9396_spec.
Lemma lem1346993 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem1346994 {A : Type'} (x : A) (a : A) (h1 : x = a) : a = x.
Proof. exact (SYM (@lem1346993 A x a h1)). Qed.
Lemma lem1346995 {A : Type'} (a : A) (x : A) (h1 : a = x) : a = x.
Proof. exact (h1). Qed.
Lemma lem1346996 {A : Type'} (a : A) (x : A) (h1 : a = x) : x = a.
Proof. exact (SYM (@lem1346995 A a x h1)). Qed.
Lemma lem1346997 {A : Type'} (a : A) (x : A) : (x = a) = (a = x).
Proof. exact (prop_ext (fun h1 : x = a => @lem1346994 A x a h1) (fun h1 : a = x => @lem1346996 A a x h1)). Qed.
Lemma lem1346998 {A : Type'} (a : A) : (term0 A a) = (term1 A a).
Proof. exact (fun_ext (fun x : A => @lem1346997 A a x)). Qed.
Lemma lem1346999 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1347000 {A : Type'} (a : A) : (term2 A a) = (term3 A a).
Proof. exact (MK_COMB (@lem1346999 A) (@lem1346998 A a)). Qed.
Lemma lem1347001 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (fun_ext (fun a : A => @lem1347000 A a)). Qed.
Lemma lem1347002 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1347003 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem1347002 A) (@lem1347001 A)). Qed.
Lemma lem1347004 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem1347003 A) (@lem4363 A)). Qed.
Lemma lem1347005 {A : Type'} (x : A) : term8 A x.
Proof. exact (@lem9442 A x). Qed.
Lemma lem1347006 {A : Type'} (x : A) : (term8 A x) = ((term9 A x) = x).
Proof. exact (eq_refl (term8 A x)). Qed.
Lemma lem1347007 {A : Type'} (x : A) : (term9 A x) = x.
Proof. exact (EQ_MP (@lem1347006 A x) (@lem1347005 A x)). Qed.
Lemma lem1347008 {A : Type'} (x : A) : term10 A x.
Proof. exact (@lem362 A x). Qed.
Lemma lem1347009 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (eq_refl (term10 A x)). Qed.
Lemma lem1347010 {A : Type'} (x : A) : term11 A x.
Proof. exact (EQ_MP (@lem1347009 A x) (@lem1347008 A x)). Qed.
Lemma lem1347011 {A : Type'} (x : A) (y : A) : term12 A x y.
Proof. exact (@lem1347010 A x y). Qed.
Lemma lem1347012 {A : Type'} (y : A) (x : A) : (term12 A x y) = ((x = y) = (y = x)).
Proof. exact (eq_refl (term12 A x y)). Qed.
Lemma lem1347015 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem1347012 A y x) (@lem1347011 A x y)). Qed.
Lemma lem1347016 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (@lem1347015 A y x). Qed.
Lemma lem1347017 {A : Type'} (x : A) (y : A) : (y = x) = (x = y).
Proof. exact (@lem1347016 A x y). Qed.
Lemma lem1347018 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (fun_ext (fun y : A => @lem1347017 A x y)). Qed.
Lemma lem1347019 {A : Type'} : (@ε A) = (@ε A).
Proof. exact (eq_refl (@ε A)). Qed.
Lemma lem1347020 {A : Type'} (x : A) : (term9 A x) = (term13 A x).
Proof. exact (MK_COMB (@lem1347019 A) (@lem1347018 A x)). Qed.
Lemma lem1347021 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1347022 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (MK_COMB (@lem1347021 A) (@lem1347020 A x)). Qed.
Lemma lem1347023 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1347024 {A : Type'} (x : A) : ((term9 A x) = x) = ((term13 A x) = x).
Proof. exact (MK_COMB (@lem1347022 A x) (@lem1347023 A x)). Qed.
Lemma lem1347028 (x : hreal) (y : hreal) (h1 : (term16 y x) = (x = y)) : (term16 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1347029 (x : hreal) (y : hreal) (h1 : (term16 y x) = (x = y)) : (x = y) = (term16 y x).
Proof. exact (SYM (@lem1347028 x y h1)). Qed.
Lemma lem1347030 (y : hreal) (x : hreal) (h1 : (x = y) = (term16 y x)) : (x = y) = (term16 y x).
Proof. exact (h1). Qed.
Lemma lem1347031 (y : hreal) (x : hreal) (h1 : (x = y) = (term16 y x)) : (term16 y x) = (x = y).
Proof. exact (SYM (@lem1347030 y x h1)). Qed.
Lemma lem1347032 (y : hreal) (x : hreal) : ((term16 y x) = (x = y)) = ((x = y) = (term16 y x)).
Proof. exact (prop_ext (fun h1 : (term16 y x) = (x = y) => @lem1347029 x y h1) (fun h1 : (x = y) = (term16 y x) => @lem1347031 y x h1)). Qed.
Lemma lem1347033 (x : hreal) : (term17 x) = (term18 x).
Proof. exact (fun_ext (fun y : hreal => @lem1347032 y x)). Qed.
Lemma lem1347034 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1347035 (x : hreal) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem1347034) (@lem1347033 x)). Qed.
Lemma lem1347036 : term21 = term22.
Proof. exact (fun_ext (fun x : hreal => @lem1347035 x)). Qed.
Lemma lem1347037 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1347038 : term23 = term24.
Proof. exact (MK_COMB (@lem1347037) (@lem1347036)). Qed.
Lemma lem1347039 : term24.
Proof. exact (EQ_MP (@lem1347038) (@lem1319377)). Qed.
Lemma lem1347042 (x : real) (y : real) (h1 : (term25 y x) = (x = y)) : (term25 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1347043 (x : real) (y : real) (h1 : (term25 y x) = (x = y)) : (x = y) = (term25 y x).
Proof. exact (SYM (@lem1347042 x y h1)). Qed.
Lemma lem1347044 (y : real) (x : real) (h1 : (x = y) = (term25 y x)) : (x = y) = (term25 y x).
Proof. exact (h1). Qed.
Lemma lem1347045 (y : real) (x : real) (h1 : (x = y) = (term25 y x)) : (term25 y x) = (x = y).
Proof. exact (SYM (@lem1347044 y x h1)). Qed.
Lemma lem1347046 (y : real) (x : real) : ((term25 y x) = (x = y)) = ((x = y) = (term25 y x)).
Proof. exact (prop_ext (fun h1 : (term25 y x) = (x = y) => @lem1347043 x y h1) (fun h1 : (x = y) = (term25 y x) => @lem1347045 y x h1)). Qed.
Lemma lem1347047 (x : real) : (term26 x) = (term27 x).
Proof. exact (fun_ext (fun y : real => @lem1347046 y x)). Qed.
Lemma lem1347048 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1347049 (x : real) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem1347048) (@lem1347047 x)). Qed.
Lemma lem1347050 : term30 = term31.
Proof. exact (fun_ext (fun x : real => @lem1347049 x)). Qed.
Lemma lem1347051 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1347052 : term32 = term33.
Proof. exact (MK_COMB (@lem1347051) (@lem1347050)). Qed.
Lemma lem1347053 : term33.
Proof. exact (EQ_MP (@lem1347052) (@lem1339379)). Qed.
Lemma lem1347054 (r : hreal -> real) (h1 : term34 r) : term34 r.
Proof. exact (h1). Qed.
Lemma lem1347055 (r : hreal -> real) (h1 : term35 r) : term35 r.
Proof. exact (h1). Qed.
Lemma lem1347056 (r : hreal -> real) (h1 : term36 r) : term36 r.
Proof. exact (h1). Qed.
Lemma lem1347063 (x : real) (r : hreal -> real) (h1 : term36 r) : term37 r x.
Proof. exact (@lem1347056 r h1 x). Qed.
Lemma lem1347064 (x : real) (r : hreal -> real) : (term37 r x) = ((term38 x) = (term39 x r)).
Proof. exact (eq_refl (term37 r x)). Qed.
Lemma lem1347066 (y : hreal) (r : hreal -> real) (h1 : term35 r) : term40 r y.
Proof. exact (@lem1347055 r h1 y). Qed.
Lemma lem1347067 (y : hreal) (r : hreal -> real) : (term40 r y) = (term41 y r).
Proof. exact (eq_refl (term40 r y)). Qed.
Lemma lem1347068 (y : hreal) (r : hreal -> real) (h1 : term35 r) : term41 y r.
Proof. exact (EQ_MP (@lem1347067 y r) (@lem1347066 y r h1)). Qed.
Lemma lem1347069 (y : hreal) (z : hreal) (r : hreal -> real) (h1 : term35 r) : term42 y r z.
Proof. exact (@lem1347068 y r h1 z). Qed.
Lemma lem1347070 (y : hreal) (r : hreal -> real) (z : hreal) : (term42 y r z) = ((hreal_le y z) = (term43 y r z)).
Proof. exact (eq_refl (term42 y r z)). Qed.
Lemma lem1347081 {A B : Type'} (f : A -> B) (y : A) : (term44 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1347082 (f : real -> hreal) (y : real) : (term45 f y) = (f y).
Proof. exact (@lem1347081 real hreal f y). Qed.
Lemma lem1347083 (r : hreal -> real) (x : hreal) : (term46 r x) = (term47 r x).
Proof. exact (@lem1347082 (term48 r) (r x)). Qed.
Lemma lem1347084 (x : real) (r : hreal -> real) : (term49 r x) = (term50 x r).
Proof. exact (eq_refl (term49 r x)). Qed.
Lemma lem1347085 (r : hreal -> real) : (term51 r) = (term48 r).
Proof. exact (fun_ext (fun x : real => @lem1347084 x r)). Qed.
Lemma lem1347086 (r : hreal -> real) (x : hreal) : (r x) = (r x).
Proof. exact (eq_refl (r x)). Qed.
Lemma lem1347087 (r : hreal -> real) (x : hreal) : (term46 r x) = (term47 r x).
Proof. exact (MK_COMB (@lem1347085 r) (@lem1347086 r x)). Qed.
Lemma lem1347088 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1347089 (r : hreal -> real) (x : hreal) : (term52 r x) = (term53 r x).
Proof. exact (MK_COMB (@lem1347088) (@lem1347087 r x)). Qed.
Lemma lem1347090 (x : hreal) (r : hreal -> real) : (term47 r x) = (term54 x r).
Proof. exact (eq_refl (term47 r x)). Qed.
Lemma lem1347091 (x : hreal) (r : hreal -> real) : ((term46 r x) = (term47 r x)) = ((term47 r x) = (term54 x r)).
Proof. exact (MK_COMB (@lem1347089 r x) (@lem1347090 x r)). Qed.
Lemma lem1347092 (x : hreal) (r : hreal -> real) : (term47 r x) = (term54 x r).
Proof. exact (EQ_MP (@lem1347091 x r) (@lem1347083 r x)). Qed.
Lemma lem1347097 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1347098 (x : hreal) (r : hreal -> real) : (term53 r x) = (term55 x r).
Proof. exact (MK_COMB (@lem1347097) (@lem1347092 x r)). Qed.
Lemma lem1347099 (x : hreal) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1347100 (r : hreal -> real) (x : hreal) : ((term47 r x) = x) = ((term54 x r) = x).
Proof. exact (MK_COMB (@lem1347098 x r) (@lem1347099 x)). Qed.
Lemma lem1347103 (r : hreal -> real) : (term56 r) = (term57 r).
Proof. exact (fun_ext (fun x : hreal => @lem1347100 r x)). Qed.
Lemma lem1347104 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1347105 (r : hreal -> real) : (term58 r) = (term59 r).
Proof. exact (MK_COMB (@lem1347104) (@lem1347103 r)). Qed.
Lemma lem1347110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1347111 (r : hreal -> real) : (term60 r) = (term61 r).
Proof. exact (MK_COMB (@lem1347110) (@lem1347105 r)). Qed.
Lemma lem1347121 (x : real) (r : hreal -> real) (h1 : term36 r) : (term38 x) = (term39 x r).
Proof. exact (EQ_MP (@lem1347064 x r) (@lem1347063 x r h1)). Qed.
Lemma lem1347128 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1347129 (x : real) (r : hreal -> real) (h1 : term36 r) : (term62 x) = (term63 x r).
Proof. exact (MK_COMB (@lem1347128) (@lem1347121 x r h1)). Qed.
Lemma lem1347133 {A B : Type'} (f : A -> B) (y : A) : (term44 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1347134 (f : real -> hreal) (y : real) : (term45 f y) = (f y).
Proof. exact (@lem1347133 real hreal f y). Qed.
Lemma lem1347135 (r : hreal -> real) (x : real) : (term64 r x) = (term49 r x).
Proof. exact (@lem1347134 (term48 r) x). Qed.
Lemma lem1347136 (x : real) (r : hreal -> real) : (term49 r x) = (term50 x r).
Proof. exact (eq_refl (term49 r x)). Qed.
Lemma lem1347137 (r : hreal -> real) : (term51 r) = (term48 r).
Proof. exact (fun_ext (fun x : real => @lem1347136 x r)). Qed.
Lemma lem1347138 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1347139 (r : hreal -> real) (x : real) : (term64 r x) = (term49 r x).
Proof. exact (MK_COMB (@lem1347137 r) (@lem1347138 x)). Qed.
Lemma lem1347140 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1347141 (r : hreal -> real) (x : real) : (term65 r x) = (term66 r x).
Proof. exact (MK_COMB (@lem1347140) (@lem1347139 r x)). Qed.
Lemma lem1347142 (x : real) (r : hreal -> real) : (term49 r x) = (term50 x r).
Proof. exact (eq_refl (term49 r x)). Qed.
Lemma lem1347143 (x : real) (r : hreal -> real) : ((term64 r x) = (term49 r x)) = ((term49 r x) = (term50 x r)).
Proof. exact (MK_COMB (@lem1347141 r x) (@lem1347142 x r)). Qed.
Lemma lem1347144 (x : real) (r : hreal -> real) : (term49 r x) = (term50 x r).
Proof. exact (EQ_MP (@lem1347143 x r) (@lem1347135 r x)). Qed.
Lemma lem1347149 (r : hreal -> real) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1347150 (x : real) (r : hreal -> real) : (term67 r x) = (term68 x r).
Proof. exact (MK_COMB (@lem1347149 r) (@lem1347144 x r)). Qed.
Lemma lem1347151 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1347152 (x : real) (r : hreal -> real) : (term69 r x) = (term70 x r).
Proof. exact (MK_COMB (@lem1347151) (@lem1347150 x r)). Qed.
Lemma lem1347153 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1347154 (r : hreal -> real) (x : real) : ((term67 r x) = x) = ((term68 x r) = x).
Proof. exact (MK_COMB (@lem1347152 x r) (@lem1347153 x)). Qed.
Lemma lem1347157 (x : real) (r : hreal -> real) (h1 : term36 r) : (term71 r x) = (term72 r x).
Proof. exact (MK_COMB (@lem1347129 x r h1) (@lem1347154 r x)). Qed.
Lemma lem1347160 (r : hreal -> real) (h1 : term36 r) : (term73 r) = (term74 r).
Proof. exact (fun_ext (fun x : real => @lem1347157 x r h1)). Qed.
Lemma lem1347161 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1347162 (r : hreal -> real) (h1 : term36 r) : (term75 r) = (term76 r).
Proof. exact (MK_COMB (@lem1347161) (@lem1347160 r h1)). Qed.
Lemma lem1347167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1347168 (r : hreal -> real) (h1 : term36 r) : (term77 r) = (term78 r).
Proof. exact (MK_COMB (@lem1347167) (@lem1347162 r h1)). Qed.
Lemma lem1347176 (x : real) (r : hreal -> real) (h1 : term36 r) : (term38 x) = (term39 x r).
Proof. exact (EQ_MP (@lem1347064 x r) (@lem1347063 x r h1)). Qed.
Lemma lem1347177 (x : hreal) (r : hreal -> real) (h1 : term36 r) : (term79 r x) = (term80 x r).
Proof. exact (@lem1347176 (r x) r h1). Qed.
Lemma lem1347184 (r : hreal -> real) (h1 : term36 r) : (term81 r) = (term82 r).
Proof. exact (fun_ext (fun x : hreal => @lem1347177 x r h1)). Qed.
Lemma lem1347185 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1347186 (r : hreal -> real) (h1 : term36 r) : (term83 r) = (term84 r).
Proof. exact (MK_COMB (@lem1347185) (@lem1347184 r h1)). Qed.
Lemma lem1347191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1347192 (r : hreal -> real) (h1 : term36 r) : (term85 r) = (term86 r).
Proof. exact (MK_COMB (@lem1347191) (@lem1347186 r h1)). Qed.
Lemma lem1347204 (y : hreal) (z : hreal) (r : hreal -> real) (h1 : term35 r) : (hreal_le y z) = (term43 y r z).
Proof. exact (EQ_MP (@lem1347070 y r z) (@lem1347069 y z r h1)). Qed.
Lemma lem1347205 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term35 r) : (hreal_le x y) = (term43 x r y).
Proof. exact (@lem1347204 x y r h1). Qed.
Lemma lem1347206 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1347207 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term35 r) : (term87 x y) = (term88 x r y).
Proof. exact (MK_COMB (@lem1347206) (@lem1347205 x y r h1)). Qed.
Lemma lem1347208 (x : hreal) (r : hreal -> real) (y : hreal) : (term43 x r y) = (term43 x r y).
Proof. exact (eq_refl (term43 x r y)). Qed.
Lemma lem1347209 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term35 r) : ((hreal_le x y) = (term43 x r y)) = ((term43 x r y) = (term43 x r y)).
Proof. exact (MK_COMB (@lem1347207 x y r h1) (@lem1347208 x r y)). Qed.
Lemma lem1347211 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1347212 (x : Prop) : (x = x) = True.
Proof. exact (@lem1347211 Prop x). Qed.
Lemma lem1347213 (x : hreal) (r : hreal -> real) (y : hreal) : ((term43 x r y) = (term43 x r y)) = True.
Proof. exact (@lem1347212 (term43 x r y)). Qed.
Lemma lem1347214 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term35 r) : ((hreal_le x y) = (term43 x r y)) = True.
Proof. exact (TRANS (@lem1347209 x y r h1) (@lem1347213 x r y)). Qed.
Lemma lem1347215 (x : hreal) (r : hreal -> real) (h1 : term35 r) : (term89 x r) = term90.
Proof. exact (fun_ext (fun y : hreal => @lem1347214 x y r h1)). Qed.
Lemma lem1347216 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1347217 (x : hreal) (r : hreal -> real) (h1 : term35 r) : (term41 x r) = term91.
Proof. exact (MK_COMB (@lem1347216) (@lem1347215 x r h1)). Qed.
Lemma lem1347219 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1347220 (t : Prop) : (term93 t) = t.
Proof. exact (@lem1347219 hreal t). Qed.
Lemma lem1347221 : term91 = True.
Proof. exact (@lem1347220 True). Qed.
Lemma lem1347222 (x : hreal) (r : hreal -> real) (h1 : term35 r) : (term41 x r) = True.
Proof. exact (TRANS (@lem1347217 x r h1) (@lem1347221)). Qed.
Lemma lem1347223 (r : hreal -> real) (h1 : term35 r) : (term94 r) = term90.
Proof. exact (fun_ext (fun x : hreal => @lem1347222 x r h1)). Qed.
Lemma lem1347224 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1347225 (r : hreal -> real) (h1 : term35 r) : (term35 r) = term91.
Proof. exact (MK_COMB (@lem1347224) (@lem1347223 r h1)). Qed.
Lemma lem1347227 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1347228 (t : Prop) : (term93 t) = t.
Proof. exact (@lem1347227 hreal t). Qed.
Lemma lem1347229 : term91 = True.
Proof. exact (@lem1347228 True). Qed.
Lemma lem1347230 (r : hreal -> real) (h1 : term35 r) : (term35 r) = True.
Proof. exact (TRANS (@lem1347225 r h1) (@lem1347229)). Qed.
Lemma lem1347231 (r : hreal -> real) (h1 : term35 r) (h2 : term36 r) : (term95 r) = (term96 r).
Proof. exact (MK_COMB (@lem1347192 r h2) (@lem1347230 r h1)). Qed.
Lemma lem1347233 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1347234 (r : hreal -> real) : (term96 r) = (term84 r).
Proof. exact (@lem1347233 (term84 r)). Qed.
Lemma lem1347245 (r : hreal -> real) (h1 : term35 r) (h2 : term36 r) : (term95 r) = (term84 r).
Proof. exact (TRANS (@lem1347231 r h1 h2) (@lem1347234 r)). Qed.
Lemma lem1347246 (r : hreal -> real) (h1 : term35 r) (h2 : term36 r) : (term97 r) = (term98 r).
Proof. exact (MK_COMB (@lem1347168 r h2) (@lem1347245 r h1 h2)). Qed.
Lemma lem1347249 (r : hreal -> real) (h1 : term35 r) (h2 : term36 r) : (term99 r) = (term100 r).
Proof. exact (MK_COMB (@lem1347111 r) (@lem1347246 r h1 h2)). Qed.
Lemma lem1347252 (r : hreal -> real) (h1 : term35 r) (h2 : term36 r) : (term100 r) = (term99 r).
Proof. exact (SYM (@lem1347249 r h1 h2)). Qed.
Lemma lem1347253 (r : hreal -> real) (h1 : term101 r) : term101 r.
Proof. exact (h1). Qed.
Lemma lem1347254 (x : hreal) : term102 x.
Proof. exact (@lem1347039 x). Qed.
Lemma lem1347255 (x : hreal) : (term102 x) = (term20 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1347256 (x : hreal) : term20 x.
Proof. exact (EQ_MP (@lem1347255 x) (@lem1347254 x)). Qed.
Lemma lem1347257 (x : hreal) (y : hreal) : term103 x y.
Proof. exact (@lem1347256 x y). Qed.
Lemma lem1347258 (y : hreal) (x : hreal) : (term103 x y) = ((x = y) = (term16 y x)).
Proof. exact (eq_refl (term103 x y)). Qed.
Lemma lem1347260 (x : real) : term104 x.
Proof. exact (@lem1347053 x). Qed.
Lemma lem1347261 (x : real) : (term104 x) = (term29 x).
Proof. exact (eq_refl (term104 x)). Qed.
Lemma lem1347262 (x : real) : term29 x.
Proof. exact (EQ_MP (@lem1347261 x) (@lem1347260 x)). Qed.
Lemma lem1347263 (x : real) (y : real) : term105 x y.
Proof. exact (@lem1347262 x y). Qed.
Lemma lem1347264 (y : real) (x : real) : (term105 x y) = ((x = y) = (term25 y x)).
Proof. exact (eq_refl (term105 x y)). Qed.
Lemma lem1347269 (y : hreal) (r : hreal -> real) (h1 : term35 r) : term40 r y.
Proof. exact (@lem1347055 r h1 y). Qed.
Lemma lem1347270 (y : hreal) (r : hreal -> real) : (term40 r y) = (term41 y r).
Proof. exact (eq_refl (term40 r y)). Qed.
Lemma lem1347271 (y : hreal) (r : hreal -> real) (h1 : term35 r) : term41 y r.
Proof. exact (EQ_MP (@lem1347270 y r) (@lem1347269 y r h1)). Qed.
Lemma lem1347272 (y : hreal) (z : hreal) (r : hreal -> real) (h1 : term35 r) : term42 y r z.
Proof. exact (@lem1347271 y r h1 z). Qed.
Lemma lem1347273 (y : hreal) (r : hreal -> real) (z : hreal) : (term42 y r z) = ((hreal_le y z) = (term43 y r z)).
Proof. exact (eq_refl (term42 y r z)). Qed.
Lemma lem1347294 (y : real) (x : real) : (x = y) = (term25 y x).
Proof. exact (EQ_MP (@lem1347264 y x) (@lem1347263 x y)). Qed.
Lemma lem1347295 (z : hreal) (r : hreal -> real) (y : hreal) : ((r y) = (r z)) = (term106 z r y).
Proof. exact (@lem1347294 (r z) (r y)). Qed.
Lemma lem1347298 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1347299 (z : hreal) (r : hreal -> real) (y : hreal) : (term107 y r z) = (term108 z r y).
Proof. exact (MK_COMB (@lem1347298) (@lem1347295 z r y)). Qed.
Lemma lem1347303 (y : hreal) (x : hreal) : (x = y) = (term16 y x).
Proof. exact (EQ_MP (@lem1347258 y x) (@lem1347257 x y)). Qed.
Lemma lem1347304 (z : hreal) (y : hreal) : (y = z) = (term16 z y).
Proof. exact (@lem1347303 z y). Qed.
Lemma lem1347308 (y : hreal) (z : hreal) (r : hreal -> real) (h1 : term35 r) : (hreal_le y z) = (term43 y r z).
Proof. exact (EQ_MP (@lem1347273 y r z) (@lem1347272 y z r h1)). Qed.
Lemma lem1347309 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1347310 (y : hreal) (z : hreal) (r : hreal -> real) (h1 : term35 r) : (term109 y z) = (term110 y r z).
Proof. exact (MK_COMB (@lem1347309) (@lem1347308 y z r h1)). Qed.
Lemma lem1347312 (y : hreal) (z : hreal) (r : hreal -> real) (h1 : term35 r) : (hreal_le y z) = (term43 y r z).
Proof. exact (EQ_MP (@lem1347273 y r z) (@lem1347272 y z r h1)). Qed.
Lemma lem1347313 (z : hreal) (y : hreal) (r : hreal -> real) (h1 : term35 r) : (hreal_le z y) = (term43 z r y).
Proof. exact (@lem1347312 z y r h1). Qed.
Lemma lem1347314 (z : hreal) (y : hreal) (r : hreal -> real) (h1 : term35 r) : (term16 z y) = (term106 z r y).
Proof. exact (MK_COMB (@lem1347310 y z r h1) (@lem1347313 z y r h1)). Qed.
Lemma lem1347317 (z : hreal) (y : hreal) (r : hreal -> real) (h1 : term35 r) : (y = z) = (term106 z r y).
Proof. exact (TRANS (@lem1347304 z y) (@lem1347314 z y r h1)). Qed.
Lemma lem1347318 (z : hreal) (y : hreal) (r : hreal -> real) (h1 : term35 r) : (((r y) = (r z)) = (y = z)) = ((term106 z r y) = (term106 z r y)).
Proof. exact (MK_COMB (@lem1347299 z r y) (@lem1347317 z y r h1)). Qed.
Lemma lem1347320 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1347321 (x : Prop) : (x = x) = True.
Proof. exact (@lem1347320 Prop x). Qed.
Lemma lem1347322 (z : hreal) (r : hreal -> real) (y : hreal) : ((term106 z r y) = (term106 z r y)) = True.
Proof. exact (@lem1347321 (term106 z r y)). Qed.
Lemma lem1347323 (y : hreal) (z : hreal) (r : hreal -> real) (h1 : term35 r) : (((r y) = (r z)) = (y = z)) = True.
Proof. exact (TRANS (@lem1347318 z y r h1) (@lem1347322 z r y)). Qed.
Lemma lem1347324 (y : hreal) (r : hreal -> real) (h1 : term35 r) : (term111 r y) = term90.
Proof. exact (fun_ext (fun z : hreal => @lem1347323 y z r h1)). Qed.
Lemma lem1347325 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1347326 (y : hreal) (r : hreal -> real) (h1 : term35 r) : (term112 r y) = term91.
Proof. exact (MK_COMB (@lem1347325) (@lem1347324 y r h1)). Qed.
Lemma lem1347328 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1347329 (t : Prop) : (term93 t) = t.
Proof. exact (@lem1347328 hreal t). Qed.
Lemma lem1347330 : term91 = True.
Proof. exact (@lem1347329 True). Qed.
Lemma lem1347331 (y : hreal) (r : hreal -> real) (h1 : term35 r) : (term112 r y) = True.
Proof. exact (TRANS (@lem1347326 y r h1) (@lem1347330)). Qed.
Lemma lem1347332 (r : hreal -> real) (h1 : term35 r) : (term113 r) = term90.
Proof. exact (fun_ext (fun y : hreal => @lem1347331 y r h1)). Qed.
Lemma lem1347333 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1347334 (r : hreal -> real) (h1 : term35 r) : (term101 r) = term91.
Proof. exact (MK_COMB (@lem1347333) (@lem1347332 r h1)). Qed.
Lemma lem1347336 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1347337 (t : Prop) : (term93 t) = t.
Proof. exact (@lem1347336 hreal t). Qed.
Lemma lem1347338 : term91 = True.
Proof. exact (@lem1347337 True). Qed.
Lemma lem1347339 (r : hreal -> real) (h1 : term35 r) : (term101 r) = True.
Proof. exact (TRANS (@lem1347334 r h1) (@lem1347338)). Qed.
Lemma lem1347340 (r : hreal -> real) (h1 : term35 r) : True = (term101 r).
Proof. exact (SYM (@lem1347339 r h1)). Qed.
Lemma lem1347341 (r : hreal -> real) (h1 : term35 r) : term101 r.
Proof. exact (EQ_MP (@lem1347340 r h1) (@lem0)). Qed.
Lemma lem1347342 {A : Type'} (a : A) : term114 A a.
Proof. exact (@lem1347004 A a). Qed.
Lemma lem1347343 {A : Type'} (a : A) : (term114 A a) = (term3 A a).
Proof. exact (eq_refl (term114 A a)). Qed.
Lemma lem1347344 {A : Type'} (a : A) : term3 A a.
Proof. exact (EQ_MP (@lem1347343 A a) (@lem1347342 A a)). Qed.
Lemma lem1347345 {A : Type'} (a : A) : (term3 A a) = ((term3 A a) = True).
Proof. exact (@lem7 (term3 A a)). Qed.
Lemma lem1347356 (y : hreal) (r : hreal -> real) (h1 : term101 r) : term115 r y.
Proof. exact (@lem1347253 r h1 y). Qed.
Lemma lem1347357 (r : hreal -> real) (y : hreal) : (term115 r y) = (term112 r y).
Proof. exact (eq_refl (term115 r y)). Qed.
Lemma lem1347358 (y : hreal) (r : hreal -> real) (h1 : term101 r) : term112 r y.
Proof. exact (EQ_MP (@lem1347357 r y) (@lem1347356 y r h1)). Qed.
Lemma lem1347359 (y : hreal) (z : hreal) (r : hreal -> real) (h1 : term101 r) : term116 r y z.
Proof. exact (@lem1347358 y r h1 z). Qed.
Lemma lem1347360 (r : hreal -> real) (y : hreal) (z : hreal) : (term116 r y z) = (((r y) = (r z)) = (y = z)).
Proof. exact (eq_refl (term116 r y z)). Qed.
Lemma lem1347375 (y : hreal) (z : hreal) (r : hreal -> real) (h1 : term101 r) : ((r y) = (r z)) = (y = z).
Proof. exact (EQ_MP (@lem1347360 r y z) (@lem1347359 y z r h1)). Qed.
Lemma lem1347376 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term101 r) : ((r x) = (r y)) = (x = y).
Proof. exact (@lem1347375 x y r h1). Qed.
Lemma lem1347379 (x : hreal) (r : hreal -> real) (h1 : term101 r) : (term117 x r) = (term118 x).
Proof. exact (fun_ext (fun y : hreal => @lem1347376 x y r h1)). Qed.
Lemma lem1347380 : (@ε hreal) = (@ε hreal).
Proof. exact (eq_refl (@ε hreal)). Qed.
Lemma lem1347381 (x : hreal) (r : hreal -> real) (h1 : term101 r) : (term54 x r) = (term119 x).
Proof. exact (MK_COMB (@lem1347380) (@lem1347379 x r h1)). Qed.
Lemma lem1347385 {A : Type'} (x : A) : (term13 A x) = x.
Proof. exact (EQ_MP (@lem1347024 A x) (@lem1347007 A x)). Qed.
Lemma lem1347386 (x : hreal) : (term119 x) = x.
Proof. exact (@lem1347385 hreal x). Qed.
Lemma lem1347387 (x : hreal) (r : hreal -> real) (h1 : term101 r) : (term54 x r) = x.
Proof. exact (TRANS (@lem1347381 x r h1) (@lem1347386 x)). Qed.
Lemma lem1347388 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1347389 (x : hreal) (r : hreal -> real) (h1 : term101 r) : (term55 x r) = (@eq hreal x).
Proof. exact (MK_COMB (@lem1347388) (@lem1347387 x r h1)). Qed.
Lemma lem1347390 (x : hreal) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1347391 (x : hreal) (r : hreal -> real) (h1 : term101 r) : ((term54 x r) = x) = (x = x).
Proof. exact (MK_COMB (@lem1347389 x r h1) (@lem1347390 x)). Qed.
Lemma lem1347393 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1347394 (x : hreal) : (x = x) = True.
Proof. exact (@lem1347393 hreal x). Qed.
Lemma lem1347395 (x : hreal) (r : hreal -> real) (h1 : term101 r) : ((term54 x r) = x) = True.
Proof. exact (TRANS (@lem1347391 x r h1) (@lem1347394 x)). Qed.
Lemma lem1347396 (r : hreal -> real) (h1 : term101 r) : (term57 r) = term90.
Proof. exact (fun_ext (fun x : hreal => @lem1347395 x r h1)). Qed.
Lemma lem1347397 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1347398 (r : hreal -> real) (h1 : term101 r) : (term59 r) = term91.
Proof. exact (MK_COMB (@lem1347397) (@lem1347396 r h1)). Qed.
Lemma lem1347400 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1347401 (t : Prop) : (term93 t) = t.
Proof. exact (@lem1347400 hreal t). Qed.
Lemma lem1347402 : term91 = True.
Proof. exact (@lem1347401 True). Qed.
Lemma lem1347403 (r : hreal -> real) (h1 : term101 r) : (term59 r) = True.
Proof. exact (TRANS (@lem1347398 r h1) (@lem1347402)). Qed.
Lemma lem1347404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1347405 (r : hreal -> real) (h1 : term101 r) : (term61 r) = (and True).
Proof. exact (MK_COMB (@lem1347404) (@lem1347403 r h1)). Qed.
Lemma lem1347441 (y : hreal) (z : hreal) (r : hreal -> real) (h1 : term101 r) : ((r y) = (r z)) = (y = z).
Proof. exact (EQ_MP (@lem1347360 r y z) (@lem1347359 y z r h1)). Qed.
Lemma lem1347442 (x : hreal) (y : hreal) (r : hreal -> real) (h1 : term101 r) : ((r x) = (r y)) = (x = y).
Proof. exact (@lem1347441 x y r h1). Qed.
Lemma lem1347445 (x : hreal) (r : hreal -> real) (h1 : term101 r) : (term117 x r) = (term118 x).
Proof. exact (fun_ext (fun y : hreal => @lem1347442 x y r h1)). Qed.
Lemma lem1347446 : (@ex hreal) = (@ex hreal).
Proof. exact (eq_refl (@ex hreal)). Qed.
Lemma lem1347447 (x : hreal) (r : hreal -> real) (h1 : term101 r) : (term80 x r) = (term120 x).
Proof. exact (MK_COMB (@lem1347446) (@lem1347445 x r h1)). Qed.
Lemma lem1347449 {A : Type'} (a : A) : (term3 A a) = True.
Proof. exact (EQ_MP (@lem1347345 A a) (@lem1347344 A a)). Qed.
Lemma lem1347450 (a : hreal) : (term120 a) = True.
Proof. exact (@lem1347449 hreal a). Qed.
Lemma lem1347451 (x : hreal) : (term120 x) = True.
Proof. exact (@lem1347450 x). Qed.
Lemma lem1347452 (x : hreal) (r : hreal -> real) (h1 : term101 r) : (term80 x r) = True.
Proof. exact (TRANS (@lem1347447 x r h1) (@lem1347451 x)). Qed.
Lemma lem1347453 (r : hreal -> real) (h1 : term101 r) : (term82 r) = term90.
Proof. exact (fun_ext (fun x : hreal => @lem1347452 x r h1)). Qed.
Lemma lem1347454 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1347455 (r : hreal -> real) (h1 : term101 r) : (term84 r) = term91.
Proof. exact (MK_COMB (@lem1347454) (@lem1347453 r h1)). Qed.
Lemma lem1347457 {A : Type'} (t : Prop) : (term92 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1347458 (t : Prop) : (term93 t) = t.
Proof. exact (@lem1347457 hreal t). Qed.
Lemma lem1347459 : term91 = True.
Proof. exact (@lem1347458 True). Qed.
Lemma lem1347460 (r : hreal -> real) (h1 : term101 r) : (term84 r) = True.
Proof. exact (TRANS (@lem1347455 r h1) (@lem1347459)). Qed.
Lemma lem1347461 (r : hreal -> real) : (term78 r) = (term78 r).
Proof. exact (eq_refl (term78 r)). Qed.
Lemma lem1347462 (r : hreal -> real) (h1 : term101 r) : (term98 r) = (term121 r).
Proof. exact (MK_COMB (@lem1347461 r) (@lem1347460 r h1)). Qed.
Lemma lem1347464 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1347465 (r : hreal -> real) : (term121 r) = (term76 r).
Proof. exact (@lem1347464 (term76 r)). Qed.
Lemma lem1347488 (r : hreal -> real) (h1 : term101 r) : (term98 r) = (term76 r).
Proof. exact (TRANS (@lem1347462 r h1) (@lem1347465 r)). Qed.
Lemma lem1347489 (r : hreal -> real) (h1 : term101 r) : (term100 r) = (term122 r).
Proof. exact (MK_COMB (@lem1347405 r h1) (@lem1347488 r h1)). Qed.
Lemma lem1347491 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1347492 (r : hreal -> real) : (term122 r) = (term76 r).
Proof. exact (@lem1347491 (term76 r)). Qed.
Lemma lem1347515 (r : hreal -> real) (h1 : term101 r) : (term100 r) = (term76 r).
Proof. exact (TRANS (@lem1347489 r h1) (@lem1347492 r)). Qed.
Lemma lem1347516 (r : hreal -> real) (h1 : term101 r) : (term76 r) = (term100 r).
Proof. exact (SYM (@lem1347515 r h1)). Qed.
Lemma lem1347517 (x : real) (r : hreal -> real) (h1 : term39 x r) : term39 x r.
Proof. exact (h1). Qed.
Lemma lem1347518 (P : hreal -> Prop) : term123 P.
Proof. exact (@lem9396 hreal P). Qed.
Lemma lem1347519 (x : real) (r : hreal -> real) : term124 x r.
Proof. exact (@lem1347518 (term125 x r)). Qed.
Lemma lem1347520 (x : real) (r : hreal -> real) (h1 : term39 x r) : term126 x r.
Proof. exact (@lem1347519 x r (@lem1347517 x r h1)). Qed.
Lemma lem1347521 (x : real) (r : hreal -> real) : (term126 x r) = (x = (term68 x r)).
Proof. exact (eq_refl (term126 x r)). Qed.
Lemma lem1347522 (x : real) (r : hreal -> real) (h1 : term39 x r) : x = (term68 x r).
Proof. exact (EQ_MP (@lem1347521 x r) (@lem1347520 x r h1)). Qed.
Lemma lem1347523 (x : real) (r : hreal -> real) (h1 : term39 x r) : (term68 x r) = x.
Proof. exact (SYM (@lem1347522 x r h1)). Qed.
Lemma lem1347524 (r : hreal -> real) (x : real) : term72 r x.
Proof. exact (fun h0 : term39 x r => @lem1347523 x r h0). Qed.
Lemma lem1347529 (r : hreal -> real) : term76 r.
Proof. exact (fun x : real => @lem1347524 r x). Qed.
Lemma lem1347530 (r : hreal -> real) (h1 : term101 r) : term100 r.
Proof. exact (EQ_MP (@lem1347516 r h1) (@lem1347529 r)). Qed.
Lemma lem1347531 (r : hreal -> real) (h1 : term101 r) : (term101 r) = (term100 r).
Proof. exact (prop_ext (fun h2 : term101 r => @lem1347530 r h1) (fun h2 : term100 r => @lem1347253 r h1)). Qed.
Lemma lem1347532 (r : hreal -> real) (h1 : term101 r) : term100 r.
Proof. exact (EQ_MP (@lem1347531 r h1) (@lem1347253 r h1)). Qed.
Lemma lem1347533 (r : hreal -> real) (h1 : term35 r) : (term101 r) = (term100 r).
Proof. exact (prop_ext (fun h2 : term101 r => @lem1347532 r h2) (fun h2 : term100 r => @lem1347341 r h1)). Qed.
Lemma lem1347534 (r : hreal -> real) (h1 : term35 r) : term100 r.
Proof. exact (EQ_MP (@lem1347533 r h1) (@lem1347341 r h1)). Qed.
Lemma lem1347535 (r : hreal -> real) (h1 : term35 r) (h2 : term36 r) : term99 r.
Proof. exact (EQ_MP (@lem1347252 r h1 h2) (@lem1347534 r h1)). Qed.
Lemma lem1347536 (r : hreal -> real) (h1 : term35 r) (h2 : term36 r) : term127 r.
Proof. exact (ex_intro (term128 r) r (@lem1347535 r h1 h2)). Qed.
Lemma lem1347537 (r : hreal -> real) (h1 : term35 r) (h2 : term36 r) : term129.
Proof. exact (ex_intro term130 (term48 r) (@lem1347536 r h1 h2)). Qed.
Lemma lem1347538 (r : hreal -> real) (h1 : term34 r) : term35 r.
Proof. exact (proj2 (@lem1347054 r h1)). Qed.
Lemma lem1347539 (r : hreal -> real) (h1 : term34 r) : term36 r.
Proof. exact (proj1 (@lem1347054 r h1)). Qed.
Lemma lem1347540 (r : hreal -> real) (h1 : term35 r) (h2 : term36 r) : (term35 r) = term129.
Proof. exact (prop_ext (fun h3 : term35 r => @lem1347537 r h1 h2) (fun h3 : term129 => @lem1347055 r h1)). Qed.
Lemma lem1347541 (r : hreal -> real) (h1 : term35 r) (h2 : term36 r) : term129.
Proof. exact (EQ_MP (@lem1347540 r h1 h2) (@lem1347055 r h1)). Qed.
Lemma lem1347542 (r : hreal -> real) (h1 : term35 r) (h2 : term36 r) : (term36 r) = term129.
Proof. exact (prop_ext (fun h3 : term36 r => @lem1347541 r h1 h2) (fun h3 : term129 => @lem1347056 r h2)). Qed.
Lemma lem1347543 (r : hreal -> real) (h1 : term35 r) (h2 : term36 r) : term129.
Proof. exact (EQ_MP (@lem1347542 r h1 h2) (@lem1347056 r h2)). Qed.
Lemma lem1347544 (r : hreal -> real) (h1 : term36 r) (h2 : term34 r) : (term35 r) = term129.
Proof. exact (prop_ext (fun h3 : term35 r => @lem1347543 r h3 h1) (fun h3 : term129 => @lem1347538 r h2)). Qed.
Lemma lem1347545 (r : hreal -> real) (h1 : term36 r) (h2 : term34 r) : term129.
Proof. exact (EQ_MP (@lem1347544 r h1 h2) (@lem1347538 r h2)). Qed.
Lemma lem1347546 (r : hreal -> real) (h1 : term34 r) : (term36 r) = term129.
Proof. exact (prop_ext (fun h2 : term36 r => @lem1347545 r h2 h1) (fun h2 : term129 => @lem1347539 r h1)). Qed.
Lemma lem1347547 (r : hreal -> real) (h1 : term34 r) : term129.
Proof. exact (EQ_MP (@lem1347546 r h1) (@lem1347539 r h1)). Qed.
Lemma lem1347548 : term129.
Proof. exact (ex_elim (@lem1346990) (fun r : hreal -> real => fun h0 : term131 r => @lem1347547 r h0)). Qed.
