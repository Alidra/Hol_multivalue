Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_REFL_term_abbrevs.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Lemma lem1505094 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1505095 : term2 = term3.
Proof. exact (@lem1505094 term4). Qed.
Lemma lem1505096 (x : real) : (term5 x) = ((real_sub x x) = term6).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1505097 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1505099 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1505097) (@lem1505096 x)). Qed.
Lemma lem1505100 : term9 = term10.
Proof. exact (fun_ext (fun x : real => @lem1505099 x)). Qed.
Lemma lem1505101 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505102 : term3 = term11.
Proof. exact (MK_COMB (@lem1505101) (@lem1505100)). Qed.
Lemma lem1505104 : term2 = term11.
Proof. exact (TRANS (@lem1505095) (@lem1505102)). Qed.
Lemma lem1505107 (x : real) : (term8 x) = (term8 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1505108 : term10 = term10.
Proof. exact (fun_ext (fun x : real => @lem1505107 x)). Qed.
Lemma lem1505109 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505110 : term11 = term11.
Proof. exact (MK_COMB (@lem1505109) (@lem1505108)). Qed.
Lemma lem1505111 : term2 = term11.
Proof. exact (TRANS (@lem1505104) (@lem1505110)). Qed.
Lemma lem1505112 (x : real) : (term8 x) = (term12 x).
Proof. exact (@lem1483554 (real_sub x x) term6). Qed.
Lemma lem1505113 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1505119 (x : real) : (real_sub x x) = (term13 x).
Proof. exact (@lem1483519 x x). Qed.
Lemma lem1505123 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1483442 term15 x). Qed.
Lemma lem1505125 (m : nat) : (term16 m) = term6.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1505126 : term17 = term6.
Proof. exact (@lem1505125 term18). Qed.
Lemma lem1505127 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1505128 : term19 = term20.
Proof. exact (MK_COMB (@lem1505127) (@lem1505126)). Qed.
Lemma lem1505129 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1505130 (x : real) : (term14 x) = (term21 x).
Proof. exact (MK_COMB (@lem1505128) (@lem1505129 x)). Qed.
Lemma lem1505131 (x : real) : (term13 x) = (term21 x).
Proof. exact (TRANS (@lem1505123 x) (@lem1505130 x)). Qed.
Lemma lem1505132 (x : real) : (term21 x) = term6.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1505134 (x : real) : (term13 x) = term6.
Proof. exact (TRANS (@lem1505131 x) (@lem1505132 x)). Qed.
Lemma lem1505136 (x : real) : (real_sub x x) = term6.
Proof. exact (TRANS (@lem1505119 x) (@lem1505134 x)). Qed.
Lemma lem1505137 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1505138 (x : real) : (term22 x) = term23.
Proof. exact (MK_COMB (@lem1505137) (@lem1505136 x)). Qed.
Lemma lem1505139 (x : real) : (term24 x) = term25.
Proof. exact (MK_COMB (@lem1505138 x) (@lem1505113)). Qed.
Lemma lem1505140 : term25 = term26.
Proof. exact (@lem1483519 term6 term6). Qed.
Lemma lem1505142 (x : nat) : (term27 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1505143 : term28 = term6.
Proof. exact (@lem1505142 term18). Qed.
Lemma lem1505144 : term29 = term29.
Proof. exact (eq_refl term29). Qed.
Lemma lem1505145 : term26 = term30.
Proof. exact (MK_COMB (@lem1505144) (@lem1505143)). Qed.
Lemma lem1505146 : term30 = term6.
Proof. exact (@lem1483448 term6). Qed.
Lemma lem1505147 : term26 = term6.
Proof. exact (TRANS (@lem1505145) (@lem1505146)). Qed.
Lemma lem1505148 : term25 = term6.
Proof. exact (TRANS (@lem1505140) (@lem1505147)). Qed.
Lemma lem1505149 (x : real) : (term24 x) = term6.
Proof. exact (TRANS (@lem1505139 x) (@lem1505148)). Qed.
Lemma lem1505150 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1505151 (x : real) : (term31 x) = term32.
Proof. exact (MK_COMB (@lem1505150) (@lem1505149 x)). Qed.
Lemma lem1505152 : term32 = term28.
Proof. exact (@lem1483512 term6). Qed.
Lemma lem1505154 (x : nat) : (term27 x) = term6.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1505155 : term28 = term6.
Proof. exact (@lem1505154 term18). Qed.
Lemma lem1505156 : term32 = term6.
Proof. exact (TRANS (@lem1505152) (@lem1505155)). Qed.
Lemma lem1505157 (x : real) : (term33 x) = (term33 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1505158 (x : real) : ((term31 x) = term32) = ((term31 x) = term6).
Proof. exact (MK_COMB (@lem1505157 x) (@lem1505156)). Qed.
Lemma lem1505159 (x : real) : (term31 x) = term6.
Proof. exact (EQ_MP (@lem1505158 x) (@lem1505151 x)). Qed.
Lemma lem1505160 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1505161 (x : real) : (term34 x) = term35.
Proof. exact (MK_COMB (@lem1505160) (@lem1505159 x)). Qed.
Lemma lem1505162 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1505163 (x : real) : (term36 x) = term37.
Proof. exact (MK_COMB (@lem1505161 x) (@lem1505162)). Qed.
Lemma lem1505164 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1505165 (x : real) : (term38 x) = term35.
Proof. exact (MK_COMB (@lem1505164) (@lem1505149 x)). Qed.
Lemma lem1505166 : term6 = term6.
Proof. exact (eq_refl term6). Qed.
Lemma lem1505167 (x : real) : (term39 x) = term37.
Proof. exact (MK_COMB (@lem1505165 x) (@lem1505166)). Qed.
Lemma lem1505168 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1505169 (x : real) : (term40 x) = term41.
Proof. exact (MK_COMB (@lem1505168) (@lem1505167 x)). Qed.
Lemma lem1505170 (x : real) : (term12 x) = term42.
Proof. exact (MK_COMB (@lem1505169 x) (@lem1505163 x)). Qed.
Lemma lem1505171 (x : real) : (term8 x) = term42.
Proof. exact (TRANS (@lem1505112 x) (@lem1505170 x)). Qed.
Lemma lem1505172 : term10 = term43.
Proof. exact (fun_ext (fun x : real => @lem1505171 x)). Qed.
Lemma lem1505173 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505174 : term11 = term44.
Proof. exact (MK_COMB (@lem1505173) (@lem1505172)). Qed.
Lemma lem1505175 : term2 = term44.
Proof. exact (TRANS (@lem1505111) (@lem1505174)). Qed.
Lemma lem1505177 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term45 A P Q) = (term46 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1505178 (P : real -> Prop) (Q : real -> Prop) : (term47 P Q) = (term48 P Q).
Proof. exact (@lem1505177 real P Q). Qed.
Lemma lem1505179 : term49 = term50.
Proof. exact (@lem1505178 term51 term51). Qed.
Lemma lem1505180 (x : real) : (term52 x) = term37.
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1505181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1505182 (x : real) : (term53 x) = term41.
Proof. exact (MK_COMB (@lem1505181) (@lem1505180 x)). Qed.
Lemma lem1505183 (x : real) : (term52 x) = term37.
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1505184 (x : real) : (term54 x) = term42.
Proof. exact (MK_COMB (@lem1505182 x) (@lem1505183 x)). Qed.
Lemma lem1505185 : term55 = term43.
Proof. exact (fun_ext (fun x : real => @lem1505184 x)). Qed.
Lemma lem1505186 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505187 : term49 = term44.
Proof. exact (MK_COMB (@lem1505186) (@lem1505185)). Qed.
Lemma lem1505188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1505189 : term56 = term57.
Proof. exact (MK_COMB (@lem1505188) (@lem1505187)). Qed.
Lemma lem1505190 (x : real) : (term52 x) = term37.
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1505191 : term58 = term51.
Proof. exact (fun_ext (fun x : real => @lem1505190 x)). Qed.
Lemma lem1505192 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505193 : term59 = term60.
Proof. exact (MK_COMB (@lem1505192) (@lem1505191)). Qed.
Lemma lem1505194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1505195 : term61 = term62.
Proof. exact (MK_COMB (@lem1505194) (@lem1505193)). Qed.
Lemma lem1505196 (x : real) : (term52 x) = term37.
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1505197 : term58 = term51.
Proof. exact (fun_ext (fun x : real => @lem1505196 x)). Qed.
Lemma lem1505198 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1505199 : term59 = term60.
Proof. exact (MK_COMB (@lem1505198) (@lem1505197)). Qed.
Lemma lem1505200 : term50 = term63.
Proof. exact (MK_COMB (@lem1505195) (@lem1505199)). Qed.
Lemma lem1505201 : (term49 = term50) = (term44 = term63).
Proof. exact (MK_COMB (@lem1505189) (@lem1505200)). Qed.
Lemma lem1505202 : term44 = term63.
Proof. exact (EQ_MP (@lem1505201) (@lem1505179)). Qed.
Lemma lem1505204 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1505205 (t : Prop) : (term65 t) = t.
Proof. exact (@lem1505204 real t). Qed.
Lemma lem1505206 : term60 = term37.
Proof. exact (@lem1505205 term37). Qed.
Lemma lem1505207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1505208 : term62 = term41.
Proof. exact (MK_COMB (@lem1505207) (@lem1505206)). Qed.
Lemma lem1505210 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1505211 (t : Prop) : (term65 t) = t.
Proof. exact (@lem1505210 real t). Qed.
Lemma lem1505212 : term60 = term37.
Proof. exact (@lem1505211 term37). Qed.
Lemma lem1505213 : term63 = term42.
Proof. exact (MK_COMB (@lem1505208) (@lem1505212)). Qed.
Lemma lem1505216 : term44 = term42.
Proof. exact (TRANS (@lem1505202) (@lem1505213)). Qed.
Lemma lem1505225 : term2 = term42.
Proof. exact (TRANS (@lem1505175) (@lem1505216)). Qed.
Lemma lem1505235 (h1 : term42) : term42.
Proof. exact (h1). Qed.
Lemma lem1505236 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1505238 (n : nat) (m : nat) : (term66 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1505239 : term37 = term67.
Proof. exact (@lem1505238 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1505240 : term67 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1505241 : term37 = False.
Proof. exact (TRANS (@lem1505239) (@lem1505240)). Qed.
Lemma lem1505242 (h1 : term37) : False.
Proof. exact (EQ_MP (@lem1505241) (@lem1505236 h1)). Qed.
Lemma lem1505243 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1505245 (n : nat) (m : nat) : (term66 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1505246 : term37 = term67.
Proof. exact (@lem1505245 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1505247 : term67 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1505248 : term37 = False.
Proof. exact (TRANS (@lem1505246) (@lem1505247)). Qed.
Lemma lem1505249 (h1 : term37) : False.
Proof. exact (EQ_MP (@lem1505248) (@lem1505243 h1)). Qed.
Lemma lem1505250 (h1 : term42) : False.
Proof. exact (or_elim (@lem1505235 h1) (fun h0 : term37 => @lem1505242 h0) (fun h0 : term37 => @lem1505249 h0)). Qed.
Lemma lem1505252 (h1 : term42) : term42.
Proof. exact (h1). Qed.
Lemma lem1505253 (h1 : term42) : term42 = False.
Proof. exact (prop_ext (fun h2 : term42 => @lem1505250 h1) (fun h2 : False => @lem1505252 h1)). Qed.
Lemma lem1505254 (h1 : term42) : False.
Proof. exact (EQ_MP (@lem1505253 h1) (@lem1505252 h1)). Qed.
Lemma lem1505255 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem1505256 (h1 : term2) : term42.
Proof. exact (EQ_MP (@lem1505225) (@lem1505255 h1)). Qed.
Lemma lem1505257 (h1 : term2) : term42 = False.
Proof. exact (prop_ext (fun h2 : term42 => @lem1505254 h2) (fun h2 : False => @lem1505256 h1)). Qed.
Lemma lem1505258 (h1 : term2) : False.
Proof. exact (EQ_MP (@lem1505257 h1) (@lem1505256 h1)). Qed.
Lemma lem1505259 : term68.
Proof. exact (fun h0 : term2 => @lem1505258 h0). Qed.
Lemma lem1505260 : term69.
Proof. exact (@lem1386578 term70). Qed.
Lemma lem1505261 : term70.
Proof. exact (@lem1505260 (@lem1505259)). Qed.
