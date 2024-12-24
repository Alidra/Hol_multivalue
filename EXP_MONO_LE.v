Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_MONO_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXP_MONO_LE_IMP_spec.
Require Import EXP_MONO_LT_IMP_spec.
Require Import LE_REFL_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm86199_spec.
Lemma lem151922 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem151923 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem151924 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem151923 t1) (@lem151922 t1)). Qed.
Lemma lem151925 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem151924 t1 t2). Qed.
Lemma lem151926 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem151927 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem151926 t1 t2) (@lem151925 t1 t2)). Qed.
Lemma lem151928 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem151927 t1 t2 t3). Qed.
Lemma lem151929 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem151930 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem151929 t1 t2 t3) (@lem151928 t1 t2 t3)). Qed.
Lemma lem151931 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem151930 t1 t2 t3)). Qed.
Lemma lem151932 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : term7 x y n.
Proof. exact (h1). Qed.
Lemma lem151933 (x : nat) (y : nat) (n : nat) (h1 : term8 x y n) : term8 x y n.
Proof. exact (h1). Qed.
Lemma lem151934 (x : nat) (y : nat) (h1 : Peano.le x y) : Peano.le x y.
Proof. exact (h1). Qed.
Lemma lem151935 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem151980 (x : nat) : term9 x.
Proof. exact (@lem150645 x). Qed.
Lemma lem151981 (x : nat) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem151982 (x : nat) : term10 x.
Proof. exact (EQ_MP (@lem151981 x) (@lem151980 x)). Qed.
Lemma lem151983 (x : nat) (y : nat) : term11 x y.
Proof. exact (@lem151982 x y). Qed.
Lemma lem151984 (x : nat) (y : nat) : (term11 x y) = (term12 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem151985 (x : nat) (y : nat) : term12 x y.
Proof. exact (EQ_MP (@lem151984 x y) (@lem151983 x y)). Qed.
Lemma lem151986 (x : nat) (y : nat) (n : nat) : term13 x y n.
Proof. exact (@lem151985 x y n). Qed.
Lemma lem151987 (x : nat) (y : nat) (n : nat) : (term13 x y n) = (term14 x y n).
Proof. exact (eq_refl (term13 x y n)). Qed.
Lemma lem151988 (x : nat) (y : nat) (n : nat) : term14 x y n.
Proof. exact (EQ_MP (@lem151987 x y n) (@lem151986 x y n)). Qed.
Lemma lem151989 (x : nat) (y : nat) (h1 : Peano.le x y) : Peano.le x y.
Proof. exact (h1). Qed.
Lemma lem151990 (n : nat) (x : nat) (y : nat) (h1 : Peano.le x y) : term7 x y n.
Proof. exact (@lem151988 x y n (@lem151989 x y h1)). Qed.
Lemma lem151991 (x : nat) (y : nat) (n : nat) : (term7 x y n) = ((term7 x y n) = True).
Proof. exact (@lem7 (term7 x y n)). Qed.
Lemma lem151992 (n : nat) (x : nat) (y : nat) (h1 : Peano.le x y) : (term7 x y n) = True.
Proof. exact (EQ_MP (@lem151991 x y n) (@lem151990 n x y h1)). Qed.
Lemma lem152014 (x : nat) (y : nat) : (Peano.le x y) = ((Peano.le x y) = True).
Proof. exact (@lem7 (Peano.le x y)). Qed.
Lemma lem152017 (x : nat) (y : nat) (n : nat) : term15 x y n.
Proof. exact (fun h0 : Peano.le x y => @lem151992 n x y h0). Qed.
Lemma lem152019 (x : nat) (y : nat) (h1 : Peano.le x y) : (Peano.le x y) = True.
Proof. exact (EQ_MP (@lem152014 x y) (@lem151934 x y h1)). Qed.
Lemma lem152020 (x : nat) (y : nat) (h1 : Peano.le x y) : True = (Peano.le x y).
Proof. exact (SYM (@lem152019 x y h1)). Qed.
Lemma lem152021 (x : nat) (y : nat) (h1 : Peano.le x y) : Peano.le x y.
Proof. exact (EQ_MP (@lem152020 x y h1) (@lem0)). Qed.
Lemma lem152022 (n : nat) (x : nat) (y : nat) (h1 : Peano.le x y) : (term7 x y n) = True.
Proof. exact (@lem152017 x y n (@lem152021 x y h1)). Qed.
Lemma lem152023 (n : nat) (x : nat) (y : nat) (h1 : Peano.le x y) : True = (term7 x y n).
Proof. exact (SYM (@lem152022 n x y h1)). Qed.
Lemma lem152024 (n : nat) (x : nat) (y : nat) (h1 : Peano.le x y) : term7 x y n.
Proof. exact (EQ_MP (@lem152023 n x y h1) (@lem0)). Qed.
Lemma lem152043 (n : nat) : term16 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem152044 (n : nat) : (term16 n) = (Peano.le n n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem152045 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem152044 n) (@lem152043 n)). Qed.
Lemma lem152046 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem152055 : term17.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem152056 (m : nat) : term18 m.
Proof. exact (@lem152055 m). Qed.
Lemma lem152057 (m : nat) : (term18 m) = ((term19 m) = term20).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem152068 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem152069 (x : nat) : (Nat.pow x) = (Nat.pow x).
Proof. exact (eq_refl (Nat.pow x)). Qed.
Lemma lem152070 (x : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.pow x n) = (term19 x).
Proof. exact (MK_COMB (@lem152069 x) (@lem152068 n h1)). Qed.
Lemma lem152072 (m : nat) : (term19 m) = term20.
Proof. exact (EQ_MP (@lem152057 m) (@lem152056 m)). Qed.
Lemma lem152073 (x : nat) : (term19 x) = term20.
Proof. exact (@lem152072 x). Qed.
Lemma lem152074 (x : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.pow x n) = term20.
Proof. exact (TRANS (@lem152070 x n h1) (@lem152073 x)). Qed.
Lemma lem152075 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem152076 (x : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term21 x n) = term22.
Proof. exact (MK_COMB (@lem152075) (@lem152074 x n h1)). Qed.
Lemma lem152078 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem152079 (y : nat) : (Nat.pow y) = (Nat.pow y).
Proof. exact (eq_refl (Nat.pow y)). Qed.
Lemma lem152080 (y : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.pow y n) = (term19 y).
Proof. exact (MK_COMB (@lem152079 y) (@lem152078 n h1)). Qed.
Lemma lem152082 (m : nat) : (term19 m) = term20.
Proof. exact (EQ_MP (@lem152057 m) (@lem152056 m)). Qed.
Lemma lem152083 (y : nat) : (term19 y) = term20.
Proof. exact (@lem152082 y). Qed.
Lemma lem152084 (y : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.pow y n) = term20.
Proof. exact (TRANS (@lem152080 y n h1) (@lem152083 y)). Qed.
Lemma lem152085 (x : nat) (y : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term7 x y n) = term23.
Proof. exact (MK_COMB (@lem152076 x n h1) (@lem152084 y n h1)). Qed.
Lemma lem152087 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem152046 n) (@lem152045 n)). Qed.
Lemma lem152088 : term23 = True.
Proof. exact (@lem152087 term20). Qed.
Lemma lem152089 (x : nat) (y : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term7 x y n) = True.
Proof. exact (TRANS (@lem152085 x y n h1) (@lem152088)). Qed.
Lemma lem152090 (x : nat) (y : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = (term7 x y n).
Proof. exact (SYM (@lem152089 x y n h1)). Qed.
Lemma lem152091 (x : nat) (y : nat) (n : nat) (h1 : n = (NUMERAL 0)) : term7 x y n.
Proof. exact (EQ_MP (@lem152090 x y n h1) (@lem0)). Qed.
Lemma lem152093 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem152094 (x : nat) (y : nat) (n : nat) : (term8 x y n) = (term25 x y n).
Proof. exact (@lem152093 (term8 x y n)). Qed.
Lemma lem152095 (x : nat) (y : nat) (n : nat) : (term25 x y n) = (term8 x y n).
Proof. exact (SYM (@lem152094 x y n)). Qed.
Lemma lem152096 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) : term26 x y n.
Proof. exact (h1). Qed.
Lemma lem152099 (x : nat) (y : nat) (n : nat) (h1 : term27 x y n) : term27 x y n.
Proof. exact (h1). Qed.
Lemma lem152100 (x : nat) (y : nat) (n : nat) : term28 x y n.
Proof. exact (fun h0 : term27 x y n => @lem152099 x y n h0). Qed.
Lemma lem152101 (x : nat) (y : nat) (n : nat) (h1 : term28 x y n) : term28 x y n.
Proof. exact (h1). Qed.
Lemma lem152102 (x : nat) (y : nat) (n : nat) (h1 : term27 x y n) : term27 x y n.
Proof. exact (h1). Qed.
Lemma lem152103 (x : nat) (y : nat) (n : nat) (h1 : term27 x y n) (h2 : term28 x y n) : term27 x y n.
Proof. exact (@lem152101 x y n h2 (@lem152102 x y n h1)). Qed.
Lemma lem152104 (x : nat) (y : nat) (n : nat) (h1 : term27 x y n) : term29 x y n.
Proof. exact (fun h0 : term28 x y n => @lem152103 x y n h1 h0). Qed.
Lemma lem152105 (x : nat) (y : nat) (n : nat) (h1 : term28 x y n) : term28 x y n.
Proof. exact (h1). Qed.
Lemma lem152106 (x : nat) (y : nat) (n : nat) (h1 : term27 x y n) (h2 : term28 x y n) : term27 x y n.
Proof. exact (@lem152104 x y n h1 (@lem152105 x y n h2)). Qed.
Lemma lem152107 (x : nat) (y : nat) (n : nat) (h1 : term28 x y n) : term28 x y n.
Proof. exact (fun h0 : term27 x y n => @lem152106 x y n h0 h1). Qed.
Lemma lem152108 (x : nat) (y : nat) (n : nat) : term30 x y n.
Proof. exact (fun h0 : term28 x y n => @lem152107 x y n h0). Qed.
Lemma lem152111 (x : nat) (y : nat) (n : nat) : term28 x y n.
Proof. exact (@lem152108 x y n (@lem152100 x y n)). Qed.
Lemma lem152149 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem152150 : term31 = term32.
Proof. exact (@lem152149 term33). Qed.
Lemma lem152159 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem152160 : term35 = term36.
Proof. exact (MK_COMB (@lem152159) (@lem152150)). Qed.
Lemma lem152163 (x : nat) (y : nat) (n : nat) : (term37 x y n) = (term37 x y n).
Proof. exact (eq_refl (term37 x y n)). Qed.
Lemma lem152164 (x : nat) (y : nat) (n : nat) : (term38 x y n) = (term39 x y n).
Proof. exact (MK_COMB (@lem152163 x y n) (@lem152160)). Qed.
Lemma lem152167 (x : nat) (y : nat) (n : nat) : (term40 x y n) = (term40 x y n).
Proof. exact (eq_refl (term40 x y n)). Qed.
Lemma lem152168 (x : nat) (y : nat) (n : nat) : (term27 x y n) = (term41 x y n).
Proof. exact (MK_COMB (@lem152167 x y n) (@lem152164 x y n)). Qed.
Lemma lem152171 (y : nat) (n : nat) : (term42 y n) = (term43 y n).
Proof. exact (fun_ext (fun x : nat => @lem152168 x y n)). Qed.
Lemma lem152172 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152173 (y : nat) (n : nat) : (term44 y n) = (term45 y n).
Proof. exact (MK_COMB (@lem152172) (@lem152171 y n)). Qed.
Lemma lem152178 (n : nat) : (term46 n) = (term47 n).
Proof. exact (fun_ext (fun y : nat => @lem152173 y n)). Qed.
Lemma lem152179 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152180 (n : nat) : (term48 n) = (term49 n).
Proof. exact (MK_COMB (@lem152179) (@lem152178 n)). Qed.
Lemma lem152185 : term50 = term51.
Proof. exact (fun_ext (fun n : nat => @lem152180 n)). Qed.
Lemma lem152186 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152195 : term52 = term53.
Proof. exact (MK_COMB (@lem152186) (@lem152185)). Qed.
Lemma lem152202 (n : nat) (m : nat) : ((term54 m n) = (Peano.lt n m)) = ((term54 m n) = (Peano.lt n m)).
Proof. exact (eq_refl ((term54 m n) = (Peano.lt n m))). Qed.
Lemma lem152203 (m : nat) : (term55 m) = (term55 m).
Proof. exact (fun_ext (fun n : nat => @lem152202 n m)). Qed.
Lemma lem152204 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152205 (m : nat) : (term56 m) = (term56 m).
Proof. exact (MK_COMB (@lem152204) (@lem152203 m)). Qed.
Lemma lem152206 : term57 = term57.
Proof. exact (fun_ext (fun m : nat => @lem152205 m)). Qed.
Lemma lem152207 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152208 : term33 = term33.
Proof. exact (MK_COMB (@lem152207) (@lem152206)). Qed.
Lemma lem152209 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem152210 : term32 = term32.
Proof. exact (MK_COMB (@lem152209) (@lem152208)). Qed.
Lemma lem152221 (x : nat) (y : nat) (n : nat) : (term58 x y n) = (term58 x y n).
Proof. exact (eq_refl (term58 x y n)). Qed.
Lemma lem152222 (x : nat) (y : nat) : (term59 x y) = (term59 x y).
Proof. exact (fun_ext (fun n : nat => @lem152221 x y n)). Qed.
Lemma lem152223 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152224 (x : nat) (y : nat) : (term60 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem152223) (@lem152222 x y)). Qed.
Lemma lem152225 (x : nat) : (term61 x) = (term61 x).
Proof. exact (fun_ext (fun y : nat => @lem152224 x y)). Qed.
Lemma lem152226 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152227 (x : nat) : (term62 x) = (term62 x).
Proof. exact (MK_COMB (@lem152226) (@lem152225 x)). Qed.
Lemma lem152228 : term63 = term63.
Proof. exact (fun_ext (fun x : nat => @lem152227 x)). Qed.
Lemma lem152229 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152230 : term64 = term64.
Proof. exact (MK_COMB (@lem152229) (@lem152228)). Qed.
Lemma lem152231 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem152232 : term34 = term34.
Proof. exact (MK_COMB (@lem152231) (@lem152230)). Qed.
Lemma lem152233 : term36 = term36.
Proof. exact (MK_COMB (@lem152232) (@lem152210)). Qed.
Lemma lem152242 (x : nat) (y : nat) (n : nat) : (term37 x y n) = (term37 x y n).
Proof. exact (eq_refl (term37 x y n)). Qed.
Lemma lem152243 (x : nat) (y : nat) (n : nat) : (term39 x y n) = (term39 x y n).
Proof. exact (MK_COMB (@lem152242 x y n) (@lem152233)). Qed.
Lemma lem152246 (x : nat) (y : nat) (n : nat) : (term40 x y n) = (term40 x y n).
Proof. exact (eq_refl (term40 x y n)). Qed.
Lemma lem152247 (x : nat) (y : nat) (n : nat) : (term41 x y n) = (term41 x y n).
Proof. exact (MK_COMB (@lem152246 x y n) (@lem152243 x y n)). Qed.
Lemma lem152248 (y : nat) (n : nat) : (term43 y n) = (term43 y n).
Proof. exact (fun_ext (fun x : nat => @lem152247 x y n)). Qed.
Lemma lem152249 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152250 (y : nat) (n : nat) : (term45 y n) = (term45 y n).
Proof. exact (MK_COMB (@lem152249) (@lem152248 y n)). Qed.
Lemma lem152251 (n : nat) : (term47 n) = (term47 n).
Proof. exact (fun_ext (fun y : nat => @lem152250 y n)). Qed.
Lemma lem152252 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152253 (n : nat) : (term49 n) = (term49 n).
Proof. exact (MK_COMB (@lem152252) (@lem152251 n)). Qed.
Lemma lem152254 : term51 = term51.
Proof. exact (fun_ext (fun n : nat => @lem152253 n)). Qed.
Lemma lem152255 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152256 : term53 = term53.
Proof. exact (MK_COMB (@lem152255) (@lem152254)). Qed.
Lemma lem152319 : term52 = term53.
Proof. exact (TRANS (@lem152195) (@lem152256)). Qed.
Lemma lem152320 : term53 = term52.
Proof. exact (SYM (@lem152319)). Qed.
Lemma lem152322 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) : term26 x y n.
Proof. exact (h1). Qed.
Lemma lem152323 (h1 : term64) : term64.
Proof. exact (h1). Qed.
Lemma lem152324 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem152330 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : term7 x y n.
Proof. exact (h1). Qed.
Lemma lem152341 (x : nat) (y : nat) (n : nat) : (term26 x y n) = (term65 x y n).
Proof. exact (@lem17160 (Peano.le x y) (n = (NUMERAL 0))). Qed.
Lemma lem152346 (n : nat) : (term66 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem152348 (x : nat) (y : nat) : (term67 x y) = (term67 x y).
Proof. exact (eq_refl (term67 x y)). Qed.
Lemma lem152349 (x : nat) (y : nat) (n : nat) : (term68 x y n) = (term69 x y n).
Proof. exact (MK_COMB (@lem152348 x y) (@lem152346 n)). Qed.
Lemma lem152350 (x : nat) (y : nat) (n : nat) : (term70 x y n) = (term68 x y n).
Proof. exact (@lem17045 (Peano.lt x y) (term71 n)). Qed.
Lemma lem152351 (x : nat) (y : nat) (n : nat) : (term70 x y n) = (term69 x y n).
Proof. exact (TRANS (@lem152350 x y n) (@lem152349 x y n)). Qed.
Lemma lem152352 (x : nat) (y : nat) (n : nat) : (term72 x y n) = (term72 x y n).
Proof. exact (eq_refl (term72 x y n)). Qed.
Lemma lem152353 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem152354 (x : nat) (y : nat) (n : nat) : (term73 x y n) = (term74 x y n).
Proof. exact (MK_COMB (@lem152353) (@lem152351 x y n)). Qed.
Lemma lem152355 (x : nat) (y : nat) (n : nat) : (term75 x y n) = (term76 x y n).
Proof. exact (MK_COMB (@lem152354 x y n) (@lem152352 x y n)). Qed.
Lemma lem152356 (x : nat) (y : nat) (n : nat) : (term58 x y n) = (term75 x y n).
Proof. exact (@lem17265 (term77 x y n) (term72 x y n)). Qed.
Lemma lem152357 (x : nat) (y : nat) (n : nat) : (term58 x y n) = (term76 x y n).
Proof. exact (TRANS (@lem152356 x y n) (@lem152355 x y n)). Qed.
Lemma lem152358 (x : nat) (y : nat) : (term59 x y) = (term78 x y).
Proof. exact (fun_ext (fun n : nat => @lem152357 x y n)). Qed.
Lemma lem152359 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152360 (x : nat) (y : nat) : (term60 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem152359) (@lem152358 x y)). Qed.
Lemma lem152361 (x : nat) : (term61 x) = (term80 x).
Proof. exact (fun_ext (fun y : nat => @lem152360 x y)). Qed.
Lemma lem152362 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152363 (x : nat) : (term62 x) = (term81 x).
Proof. exact (MK_COMB (@lem152362) (@lem152361 x)). Qed.
Lemma lem152364 : term63 = term82.
Proof. exact (fun_ext (fun x : nat => @lem152363 x)). Qed.
Lemma lem152365 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152426 : term64 = term83.
Proof. exact (MK_COMB (@lem152365) (@lem152364)). Qed.
Lemma lem152427 (h1 : term64) : term83.
Proof. exact (EQ_MP (@lem152426) (@lem152323 h1)). Qed.
Lemma lem152431 (m : nat) (n : nat) : (term84 m n) = (Peano.le m n).
Proof. exact (@lem16933 (Peano.le m n)). Qed.
Lemma lem152433 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem152434 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem152435 (m : nat) (n : nat) : (term85 m n) = (term86 m n).
Proof. exact (MK_COMB (@lem152434) (@lem152431 m n)). Qed.
Lemma lem152436 (n : nat) (m : nat) : (term87 n m) = (term88 n m).
Proof. exact (MK_COMB (@lem152435 m n) (@lem152433 n m)). Qed.
Lemma lem152441 (n : nat) (m : nat) : (term89 n m) = (term89 n m).
Proof. exact (eq_refl (term89 n m)). Qed.
Lemma lem152442 (n : nat) (m : nat) : (term90 n m) = (term91 n m).
Proof. exact (MK_COMB (@lem152441 n m) (@lem152436 n m)). Qed.
Lemma lem152443 (n : nat) (m : nat) : ((term54 m n) = (Peano.lt n m)) = (term90 n m).
Proof. exact (@lem17784 (term54 m n) (Peano.lt n m)). Qed.
Lemma lem152444 (n : nat) (m : nat) : ((term54 m n) = (Peano.lt n m)) = (term91 n m).
Proof. exact (TRANS (@lem152443 n m) (@lem152442 n m)). Qed.
Lemma lem152445 (m : nat) : (term55 m) = (term92 m).
Proof. exact (fun_ext (fun n : nat => @lem152444 n m)). Qed.
Lemma lem152446 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152447 (m : nat) : (term56 m) = (term93 m).
Proof. exact (MK_COMB (@lem152446) (@lem152445 m)). Qed.
Lemma lem152448 : term57 = term94.
Proof. exact (fun_ext (fun m : nat => @lem152447 m)). Qed.
Lemma lem152449 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152450 : term33 = term95.
Proof. exact (MK_COMB (@lem152449) (@lem152448)). Qed.
Lemma lem152456 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem152457 (P : nat -> Prop) (Q : nat -> Prop) : (term98 P Q) = (term99 P Q).
Proof. exact (@lem152456 nat P Q). Qed.
Lemma lem152458 (m : nat) : (term100 m) = (term101 m).
Proof. exact (@lem152457 (term102 m) (term103 m)). Qed.
Lemma lem152459 (n : nat) (m : nat) : (term104 m n) = (term105 n m).
Proof. exact (eq_refl (term104 m n)). Qed.
Lemma lem152460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem152461 (n : nat) (m : nat) : (term106 m n) = (term89 n m).
Proof. exact (MK_COMB (@lem152460) (@lem152459 n m)). Qed.
Lemma lem152462 (n : nat) (m : nat) : (term107 m n) = (term88 n m).
Proof. exact (eq_refl (term107 m n)). Qed.
Lemma lem152463 (n : nat) (m : nat) : (term108 m n) = (term91 n m).
Proof. exact (MK_COMB (@lem152461 n m) (@lem152462 n m)). Qed.
Lemma lem152464 (m : nat) : (term109 m) = (term92 m).
Proof. exact (fun_ext (fun n : nat => @lem152463 n m)). Qed.
Lemma lem152465 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152466 (m : nat) : (term100 m) = (term93 m).
Proof. exact (MK_COMB (@lem152465) (@lem152464 m)). Qed.
Lemma lem152467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem152468 (m : nat) : (term110 m) = (term111 m).
Proof. exact (MK_COMB (@lem152467) (@lem152466 m)). Qed.
Lemma lem152469 (n : nat) (m : nat) : (term104 m n) = (term105 n m).
Proof. exact (eq_refl (term104 m n)). Qed.
Lemma lem152470 (m : nat) : (term112 m) = (term102 m).
Proof. exact (fun_ext (fun n : nat => @lem152469 n m)). Qed.
Lemma lem152471 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152472 (m : nat) : (term113 m) = (term114 m).
Proof. exact (MK_COMB (@lem152471) (@lem152470 m)). Qed.
Lemma lem152473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem152474 (m : nat) : (term115 m) = (term116 m).
Proof. exact (MK_COMB (@lem152473) (@lem152472 m)). Qed.
Lemma lem152475 (n : nat) (m : nat) : (term107 m n) = (term88 n m).
Proof. exact (eq_refl (term107 m n)). Qed.
Lemma lem152476 (m : nat) : (term117 m) = (term103 m).
Proof. exact (fun_ext (fun n : nat => @lem152475 n m)). Qed.
Lemma lem152477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152478 (m : nat) : (term118 m) = (term119 m).
Proof. exact (MK_COMB (@lem152477) (@lem152476 m)). Qed.
Lemma lem152479 (m : nat) : (term101 m) = (term120 m).
Proof. exact (MK_COMB (@lem152474 m) (@lem152478 m)). Qed.
Lemma lem152480 (m : nat) : ((term100 m) = (term101 m)) = ((term93 m) = (term120 m)).
Proof. exact (MK_COMB (@lem152468 m) (@lem152479 m)). Qed.
Lemma lem152481 (m : nat) : (term93 m) = (term120 m).
Proof. exact (EQ_MP (@lem152480 m) (@lem152458 m)). Qed.
Lemma lem152578 : term94 = term121.
Proof. exact (fun_ext (fun m : nat => @lem152481 m)). Qed.
Lemma lem152579 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152580 : term95 = term122.
Proof. exact (MK_COMB (@lem152579) (@lem152578)). Qed.
Lemma lem152582 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem152583 (P : nat -> Prop) (Q : nat -> Prop) : (term98 P Q) = (term99 P Q).
Proof. exact (@lem152582 nat P Q). Qed.
Lemma lem152584 : term123 = term124.
Proof. exact (@lem152583 term125 term126). Qed.
Lemma lem152585 (m : nat) : (term127 m) = (term114 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem152586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem152587 (m : nat) : (term128 m) = (term116 m).
Proof. exact (MK_COMB (@lem152586) (@lem152585 m)). Qed.
Lemma lem152588 (m : nat) : (term129 m) = (term119 m).
Proof. exact (eq_refl (term129 m)). Qed.
Lemma lem152589 (m : nat) : (term130 m) = (term120 m).
Proof. exact (MK_COMB (@lem152587 m) (@lem152588 m)). Qed.
Lemma lem152590 : term131 = term121.
Proof. exact (fun_ext (fun m : nat => @lem152589 m)). Qed.
Lemma lem152591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152592 : term123 = term122.
Proof. exact (MK_COMB (@lem152591) (@lem152590)). Qed.
Lemma lem152593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem152594 : term132 = term133.
Proof. exact (MK_COMB (@lem152593) (@lem152592)). Qed.
Lemma lem152595 (m : nat) : (term127 m) = (term114 m).
Proof. exact (eq_refl (term127 m)). Qed.
Lemma lem152596 : term134 = term125.
Proof. exact (fun_ext (fun m : nat => @lem152595 m)). Qed.
Lemma lem152597 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152598 : term135 = term136.
Proof. exact (MK_COMB (@lem152597) (@lem152596)). Qed.
Lemma lem152599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem152600 : term137 = term138.
Proof. exact (MK_COMB (@lem152599) (@lem152598)). Qed.
Lemma lem152601 (m : nat) : (term129 m) = (term119 m).
Proof. exact (eq_refl (term129 m)). Qed.
Lemma lem152602 : term139 = term126.
Proof. exact (fun_ext (fun m : nat => @lem152601 m)). Qed.
Lemma lem152603 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152604 : term140 = term141.
Proof. exact (MK_COMB (@lem152603) (@lem152602)). Qed.
Lemma lem152605 : term124 = term142.
Proof. exact (MK_COMB (@lem152600) (@lem152604)). Qed.
Lemma lem152606 : (term123 = term124) = (term122 = term142).
Proof. exact (MK_COMB (@lem152594) (@lem152605)). Qed.
Lemma lem152607 : term122 = term142.
Proof. exact (EQ_MP (@lem152606) (@lem152584)). Qed.
Lemma lem152714 : term95 = term142.
Proof. exact (TRANS (@lem152580) (@lem152607)). Qed.
Lemma lem152715 : term33 = term142.
Proof. exact (TRANS (@lem152450) (@lem152714)). Qed.
Lemma lem152716 (h1 : term33) : term142.
Proof. exact (EQ_MP (@lem152715) (@lem152324 h1)). Qed.
Lemma lem152730 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : term7 x y n.
Proof. exact (h1). Qed.
Lemma lem152750 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) : term65 x y n.
Proof. exact (EQ_MP (@lem152341 x y n) (@lem152322 x y n h1)). Qed.
Lemma lem152783 (x : nat) (y : nat) (n : nat) : (term76 x y n) = (term76 x y n).
Proof. exact (eq_refl (term76 x y n)). Qed.
Lemma lem152784 (x : nat) (y : nat) : (term78 x y) = (term78 x y).
Proof. exact (fun_ext (fun n : nat => @lem152783 x y n)). Qed.
Lemma lem152785 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152786 (x : nat) (y : nat) : (term79 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem152785) (@lem152784 x y)). Qed.
Lemma lem152787 (x : nat) : (term80 x) = (term80 x).
Proof. exact (fun_ext (fun y : nat => @lem152786 x y)). Qed.
Lemma lem152788 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152789 (x : nat) : (term81 x) = (term81 x).
Proof. exact (MK_COMB (@lem152788) (@lem152787 x)). Qed.
Lemma lem152790 : term82 = term82.
Proof. exact (fun_ext (fun x : nat => @lem152789 x)). Qed.
Lemma lem152791 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152792 : term83 = term83.
Proof. exact (MK_COMB (@lem152791) (@lem152790)). Qed.
Lemma lem152793 (h1 : term64) : term83.
Proof. exact (EQ_MP (@lem152792) (@lem152427 h1)). Qed.
Lemma lem152806 (n : nat) (m : nat) : (term88 n m) = (term88 n m).
Proof. exact (eq_refl (term88 n m)). Qed.
Lemma lem152807 (m : nat) : (term103 m) = (term103 m).
Proof. exact (fun_ext (fun n : nat => @lem152806 n m)). Qed.
Lemma lem152808 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152809 (m : nat) : (term119 m) = (term119 m).
Proof. exact (MK_COMB (@lem152808) (@lem152807 m)). Qed.
Lemma lem152810 : term126 = term126.
Proof. exact (fun_ext (fun m : nat => @lem152809 m)). Qed.
Lemma lem152811 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152812 : term141 = term141.
Proof. exact (MK_COMB (@lem152811) (@lem152810)). Qed.
Lemma lem152829 (n : nat) (m : nat) : (term105 n m) = (term105 n m).
Proof. exact (eq_refl (term105 n m)). Qed.
Lemma lem152830 (m : nat) : (term102 m) = (term102 m).
Proof. exact (fun_ext (fun n : nat => @lem152829 n m)). Qed.
Lemma lem152831 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152832 (m : nat) : (term114 m) = (term114 m).
Proof. exact (MK_COMB (@lem152831) (@lem152830 m)). Qed.
Lemma lem152833 : term125 = term125.
Proof. exact (fun_ext (fun m : nat => @lem152832 m)). Qed.
Lemma lem152834 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152835 : term136 = term136.
Proof. exact (MK_COMB (@lem152834) (@lem152833)). Qed.
Lemma lem152836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem152837 : term138 = term138.
Proof. exact (MK_COMB (@lem152836) (@lem152835)). Qed.
Lemma lem152838 : term142 = term142.
Proof. exact (MK_COMB (@lem152837) (@lem152812)). Qed.
Lemma lem152839 (h1 : term33) : term142.
Proof. exact (EQ_MP (@lem152838) (@lem152716 h1)). Qed.
Lemma lem152840 (h1 : term33) : term141.
Proof. exact (proj2 (@lem152839 h1)). Qed.
Lemma lem152841 (h1 : term33) : term136.
Proof. exact (proj1 (@lem152839 h1)). Qed.
Lemma lem152847 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : term7 x y n.
Proof. exact (h1). Qed.
Lemma lem152861 (x : nat) (y : nat) (n : nat) : (term76 x y n) = (term76 x y n).
Proof. exact (eq_refl (term76 x y n)). Qed.
Lemma lem152862 (x : nat) (y : nat) : (term78 x y) = (term78 x y).
Proof. exact (fun_ext (fun n : nat => @lem152861 x y n)). Qed.
Lemma lem152863 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152864 (x : nat) (y : nat) : (term79 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem152863) (@lem152862 x y)). Qed.
Lemma lem152865 (x : nat) : (term80 x) = (term80 x).
Proof. exact (fun_ext (fun y : nat => @lem152864 x y)). Qed.
Lemma lem152866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152867 (x : nat) : (term81 x) = (term81 x).
Proof. exact (MK_COMB (@lem152866) (@lem152865 x)). Qed.
Lemma lem152868 : term82 = term82.
Proof. exact (fun_ext (fun x : nat => @lem152867 x)). Qed.
Lemma lem152869 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152871 : term83 = term83.
Proof. exact (MK_COMB (@lem152869) (@lem152868)). Qed.
Lemma lem152872 (h1 : term64) : term83.
Proof. exact (EQ_MP (@lem152871) (@lem152793 h1)). Qed.
Lemma lem152880 (n : nat) (m : nat) : (term105 n m) = (term105 n m).
Proof. exact (eq_refl (term105 n m)). Qed.
Lemma lem152881 (m : nat) : (term102 m) = (term102 m).
Proof. exact (fun_ext (fun n : nat => @lem152880 n m)). Qed.
Lemma lem152882 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152883 (m : nat) : (term114 m) = (term114 m).
Proof. exact (MK_COMB (@lem152882) (@lem152881 m)). Qed.
Lemma lem152884 : term125 = term125.
Proof. exact (fun_ext (fun m : nat => @lem152883 m)). Qed.
Lemma lem152885 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152887 : term136 = term136.
Proof. exact (MK_COMB (@lem152885) (@lem152884)). Qed.
Lemma lem152888 (h1 : term33) : term136.
Proof. exact (EQ_MP (@lem152887) (@lem152841 h1)). Qed.
Lemma lem152896 (n : nat) (m : nat) : (term88 n m) = (term88 n m).
Proof. exact (eq_refl (term88 n m)). Qed.
Lemma lem152897 (m : nat) : (term103 m) = (term103 m).
Proof. exact (fun_ext (fun n : nat => @lem152896 n m)). Qed.
Lemma lem152898 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152899 (m : nat) : (term119 m) = (term119 m).
Proof. exact (MK_COMB (@lem152898) (@lem152897 m)). Qed.
Lemma lem152900 : term126 = term126.
Proof. exact (fun_ext (fun m : nat => @lem152899 m)). Qed.
Lemma lem152901 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem152903 : term141 = term141.
Proof. exact (MK_COMB (@lem152901) (@lem152900)). Qed.
Lemma lem152904 (h1 : term33) : term141.
Proof. exact (EQ_MP (@lem152903) (@lem152840 h1)). Qed.
Lemma lem152913 (_3046 : nat) (h1 : term64) : term143 _3046.
Proof. exact (@lem152872 h1 _3046). Qed.
Lemma lem152914 (_3046 : nat) : (term143 _3046) = (term81 _3046).
Proof. exact (eq_refl (term143 _3046)). Qed.
Lemma lem152915 (_3046 : nat) (h1 : term64) : term81 _3046.
Proof. exact (EQ_MP (@lem152914 _3046) (@lem152913 _3046 h1)). Qed.
Lemma lem152916 (_3046 : nat) (_3047 : nat) (h1 : term64) : term144 _3046 _3047.
Proof. exact (@lem152915 _3046 h1 _3047). Qed.
Lemma lem152917 (_3046 : nat) (_3047 : nat) : (term144 _3046 _3047) = (term79 _3046 _3047).
Proof. exact (eq_refl (term144 _3046 _3047)). Qed.
Lemma lem152918 (_3046 : nat) (_3047 : nat) (h1 : term64) : term79 _3046 _3047.
Proof. exact (EQ_MP (@lem152917 _3046 _3047) (@lem152916 _3046 _3047 h1)). Qed.
Lemma lem152919 (_3046 : nat) (_3047 : nat) (_3048 : nat) (h1 : term64) : term145 _3046 _3047 _3048.
Proof. exact (@lem152918 _3046 _3047 h1 _3048). Qed.
Lemma lem152920 (_3046 : nat) (_3047 : nat) (_3048 : nat) : (term145 _3046 _3047 _3048) = (term76 _3046 _3047 _3048).
Proof. exact (eq_refl (term145 _3046 _3047 _3048)). Qed.
Lemma lem152921 (_3046 : nat) (_3047 : nat) (_3048 : nat) (h1 : term64) : term76 _3046 _3047 _3048.
Proof. exact (EQ_MP (@lem152920 _3046 _3047 _3048) (@lem152919 _3046 _3047 _3048 h1)). Qed.
Lemma lem152922 (_3049 : nat) (h1 : term33) : term127 _3049.
Proof. exact (@lem152888 h1 _3049). Qed.
Lemma lem152923 (_3049 : nat) : (term127 _3049) = (term114 _3049).
Proof. exact (eq_refl (term127 _3049)). Qed.
Lemma lem152924 (_3049 : nat) (h1 : term33) : term114 _3049.
Proof. exact (EQ_MP (@lem152923 _3049) (@lem152922 _3049 h1)). Qed.
Lemma lem152925 (_3049 : nat) (_3050 : nat) (h1 : term33) : term104 _3049 _3050.
Proof. exact (@lem152924 _3049 h1 _3050). Qed.
Lemma lem152926 (_3050 : nat) (_3049 : nat) : (term104 _3049 _3050) = (term105 _3050 _3049).
Proof. exact (eq_refl (term104 _3049 _3050)). Qed.
Lemma lem152928 (_3051 : nat) (h1 : term33) : term129 _3051.
Proof. exact (@lem152904 h1 _3051). Qed.
Lemma lem152929 (_3051 : nat) : (term129 _3051) = (term119 _3051).
Proof. exact (eq_refl (term129 _3051)). Qed.
Lemma lem152930 (_3051 : nat) (h1 : term33) : term119 _3051.
Proof. exact (EQ_MP (@lem152929 _3051) (@lem152928 _3051 h1)). Qed.
Lemma lem152931 (_3051 : nat) (_3052 : nat) (h1 : term33) : term107 _3051 _3052.
Proof. exact (@lem152930 _3051 h1 _3052). Qed.
Lemma lem152932 (_3052 : nat) (_3051 : nat) : (term107 _3051 _3052) = (term88 _3052 _3051).
Proof. exact (eq_refl (term107 _3051 _3052)). Qed.
Lemma lem152935 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : term7 x y n.
Proof. exact (h1). Qed.
Lemma lem152946 (_3046 : nat) (_3047 : nat) (_3048 : nat) : (term76 _3046 _3047 _3048) = (term146 _3046 _3047 _3048).
Proof. exact (@lem151931 (term147 _3046 _3047) (_3048 = (NUMERAL 0)) (term72 _3046 _3047 _3048)). Qed.
Lemma lem152947 (_3046 : nat) (_3047 : nat) (_3048 : nat) (h1 : term64) : term146 _3046 _3047 _3048.
Proof. exact (EQ_MP (@lem152946 _3046 _3047 _3048) (@lem152921 _3046 _3047 _3048 h1)). Qed.
Lemma lem152953 (_3050 : nat) (_3049 : nat) (h1 : term33) : term105 _3050 _3049.
Proof. exact (EQ_MP (@lem152926 _3050 _3049) (@lem152925 _3049 _3050 h1)). Qed.
Lemma lem152959 (_3052 : nat) (_3051 : nat) (h1 : term33) : term88 _3052 _3051.
Proof. exact (EQ_MP (@lem152932 _3052 _3051) (@lem152931 _3051 _3052 h1)). Qed.
Lemma lem152961 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) : term54 x y.
Proof. exact (proj1 (@lem152750 x y n h1)). Qed.
Lemma lem153028 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) : term71 n.
Proof. exact (proj2 (@lem152750 x y n h1)). Qed.
Lemma lem153029 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) : term148 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem153028 x y n h1). Qed.
Lemma lem153031 (p : Prop) : (term149 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem153032 (n : nat) : (term148 n) = (term71 n).
Proof. exact (@lem153031 (n = (NUMERAL 0))). Qed.
Lemma lem153033 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) : term71 n.
Proof. exact (EQ_MP (@lem153032 n) (@lem153029 x y n h1)). Qed.
Lemma lem153035 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : term7 x y n.
Proof. exact (h1). Qed.
Lemma lem153036 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : term150 x y n.
Proof. exact (fun h0 : term151 x y n => @lem153035 x y n h1). Qed.
Lemma lem153038 (p : Prop) : (term152 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem153039 (x : nat) (y : nat) (n : nat) : (term150 x y n) = (term7 x y n).
Proof. exact (@lem153038 (term7 x y n)). Qed.
Lemma lem153040 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : term7 x y n.
Proof. exact (EQ_MP (@lem153039 x y n) (@lem153036 x y n h1)). Qed.
Lemma lem153046 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem153047 (_3049 : nat) (_3050 : nat) : (term105 _3050 _3049) = (term153 _3049 _3050).
Proof. exact (@lem153046 (term147 _3050 _3049) (term54 _3049 _3050)). Qed.
Lemma lem153053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem153054 (_3049 : nat) (_3050 : nat) : (term154 _3050 _3049) = (term155 _3049 _3050).
Proof. exact (MK_COMB (@lem153053) (@lem153047 _3049 _3050)). Qed.
Lemma lem153060 (_3049 : nat) (_3050 : nat) : (term153 _3049 _3050) = (term153 _3049 _3050).
Proof. exact (eq_refl (term153 _3049 _3050)). Qed.
Lemma lem153061 (_3049 : nat) (_3050 : nat) : ((term105 _3050 _3049) = (term153 _3049 _3050)) = ((term153 _3049 _3050) = (term153 _3049 _3050)).
Proof. exact (MK_COMB (@lem153054 _3049 _3050) (@lem153060 _3049 _3050)). Qed.
Lemma lem153063 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem153064 (x : Prop) : (x = x) = True.
Proof. exact (@lem153063 Prop x). Qed.
Lemma lem153065 (_3049 : nat) (_3050 : nat) : ((term153 _3049 _3050) = (term153 _3049 _3050)) = True.
Proof. exact (@lem153064 (term153 _3049 _3050)). Qed.
Lemma lem153066 (_3049 : nat) (_3050 : nat) : ((term105 _3050 _3049) = (term153 _3049 _3050)) = True.
Proof. exact (TRANS (@lem153061 _3049 _3050) (@lem153065 _3049 _3050)). Qed.
Lemma lem153067 (_3049 : nat) (_3050 : nat) : True = ((term105 _3050 _3049) = (term153 _3049 _3050)).
Proof. exact (SYM (@lem153066 _3049 _3050)). Qed.
Lemma lem153068 (_3049 : nat) (_3050 : nat) : (term105 _3050 _3049) = (term153 _3049 _3050).
Proof. exact (EQ_MP (@lem153067 _3049 _3050) (@lem0)). Qed.
Lemma lem153069 (_3049 : nat) (_3050 : nat) (h1 : term33) : term153 _3049 _3050.
Proof. exact (EQ_MP (@lem153068 _3049 _3050) (@lem152953 _3050 _3049 h1)). Qed.
Lemma lem153071 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem153072 (_3050 : nat) (_3049 : nat) : (term153 _3049 _3050) = (term157 _3050 _3049).
Proof. exact (@lem153071 (term54 _3049 _3050) (term147 _3050 _3049)). Qed.
Lemma lem153074 (a : Prop) : (term158 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem153075 (_3049 : nat) (_3050 : nat) : (term84 _3049 _3050) = (Peano.le _3049 _3050).
Proof. exact (@lem153074 (Peano.le _3049 _3050)). Qed.
Lemma lem153076 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem153077 (_3049 : nat) (_3050 : nat) : (term159 _3049 _3050) = (term160 _3049 _3050).
Proof. exact (MK_COMB (@lem153076) (@lem153075 _3049 _3050)). Qed.
Lemma lem153078 (_3050 : nat) (_3049 : nat) : (term147 _3050 _3049) = (term147 _3050 _3049).
Proof. exact (eq_refl (term147 _3050 _3049)). Qed.
Lemma lem153079 (_3050 : nat) (_3049 : nat) : (term157 _3050 _3049) = (term161 _3050 _3049).
Proof. exact (MK_COMB (@lem153077 _3049 _3050) (@lem153078 _3050 _3049)). Qed.
Lemma lem153080 (_3050 : nat) (_3049 : nat) : (term153 _3049 _3050) = (term161 _3050 _3049).
Proof. exact (TRANS (@lem153072 _3050 _3049) (@lem153079 _3050 _3049)). Qed.
Lemma lem153083 (_3050 : nat) (_3049 : nat) (h1 : term33) : term161 _3050 _3049.
Proof. exact (EQ_MP (@lem153080 _3050 _3049) (@lem153069 _3049 _3050 h1)). Qed.
Lemma lem153084 (y : nat) (x : nat) (n : nat) (h1 : term33) : term162 y x n.
Proof. exact (@lem153083 (Nat.pow y n) (Nat.pow x n) h1). Qed.
Lemma lem153087 (x : nat) (y : nat) (n : nat) (h1 : term33) (h2 : term7 x y n) : term163 y x n.
Proof. exact (@lem153084 y x n h1 (@lem153040 x y n h2)). Qed.
Lemma lem153088 (x : nat) (y : nat) (n : nat) (h1 : term33) (h2 : term7 x y n) : term164 y x n.
Proof. exact (fun h0 : term72 y x n => @lem153087 x y n h1 h2). Qed.
Lemma lem153090 (p : Prop) : (term149 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem153091 (y : nat) (x : nat) (n : nat) : (term164 y x n) = (term163 y x n).
Proof. exact (@lem153090 (term72 y x n)). Qed.
Lemma lem153092 (x : nat) (y : nat) (n : nat) (h1 : term33) (h2 : term7 x y n) : term163 y x n.
Proof. exact (EQ_MP (@lem153091 y x n) (@lem153088 x y n h1 h2)). Qed.
Lemma lem153094 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem153095 (_3048 : nat) (_3046 : nat) (_3047 : nat) : (term146 _3046 _3047 _3048) = (term165 _3048 _3046 _3047).
Proof. exact (@lem153094 (term166 _3046 _3047 _3048) (term147 _3046 _3047)). Qed.
Lemma lem153097 (a : Prop) (b : Prop) : (term167 a b) = (term168 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem153098 (_3046 : nat) (_3047 : nat) (_3048 : nat) : (term169 _3046 _3047 _3048) = (term170 _3046 _3047 _3048).
Proof. exact (@lem153097 (_3048 = (NUMERAL 0)) (term72 _3046 _3047 _3048)). Qed.
Lemma lem153099 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem153100 (_3046 : nat) (_3047 : nat) (_3048 : nat) : (term171 _3046 _3047 _3048) = (term172 _3046 _3047 _3048).
Proof. exact (MK_COMB (@lem153099) (@lem153098 _3046 _3047 _3048)). Qed.
Lemma lem153101 (_3046 : nat) (_3047 : nat) : (term147 _3046 _3047) = (term147 _3046 _3047).
Proof. exact (eq_refl (term147 _3046 _3047)). Qed.
Lemma lem153102 (_3048 : nat) (_3046 : nat) (_3047 : nat) : (term165 _3048 _3046 _3047) = (term173 _3048 _3046 _3047).
Proof. exact (MK_COMB (@lem153100 _3046 _3047 _3048) (@lem153101 _3046 _3047)). Qed.
Lemma lem153103 (_3048 : nat) (_3046 : nat) (_3047 : nat) : (term146 _3046 _3047 _3048) = (term173 _3048 _3046 _3047).
Proof. exact (TRANS (@lem153095 _3048 _3046 _3047) (@lem153102 _3048 _3046 _3047)). Qed.
Lemma lem153105 (x : nat) (y : nat) (n : nat) (h1 : term33) (h2 : term26 x y n) (h3 : term7 x y n) : term170 y x n.
Proof. exact (conj (@lem153033 x y n h2) (@lem153092 x y n h1 h3)). Qed.
Lemma lem153107 (_3048 : nat) (_3046 : nat) (_3047 : nat) (h1 : term64) : term173 _3048 _3046 _3047.
Proof. exact (EQ_MP (@lem153103 _3048 _3046 _3047) (@lem152947 _3046 _3047 _3048 h1)). Qed.
Lemma lem153108 (n : nat) (y : nat) (x : nat) (h1 : term64) : term173 n y x.
Proof. exact (@lem153107 n y x h1). Qed.
Lemma lem153111 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : term147 y x.
Proof. exact (@lem153108 n y x h1 (@lem153105 x y n h2 h3 h4)). Qed.
Lemma lem153112 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : term174 y x.
Proof. exact (fun h0 : Peano.lt y x => @lem153111 x y n h1 h2 h3 h4). Qed.
Lemma lem153114 (p : Prop) : (term149 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem153115 (y : nat) (x : nat) : (term174 y x) = (term147 y x).
Proof. exact (@lem153114 (Peano.lt y x)). Qed.
Lemma lem153116 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : term147 y x.
Proof. exact (EQ_MP (@lem153115 y x) (@lem153112 x y n h1 h2 h3 h4)). Qed.
Lemma lem153118 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem153121 (_3051 : nat) (_3052 : nat) : (term88 _3052 _3051) = (term175 _3051 _3052).
Proof. exact (@lem153118 (Peano.lt _3052 _3051) (Peano.le _3051 _3052)). Qed.
Lemma lem153124 (_3051 : nat) (_3052 : nat) (h1 : term33) : term175 _3051 _3052.
Proof. exact (EQ_MP (@lem153121 _3051 _3052) (@lem152959 _3052 _3051 h1)). Qed.
Lemma lem153125 (x : nat) (y : nat) (h1 : term33) : term175 x y.
Proof. exact (@lem153124 x y h1). Qed.
Lemma lem153128 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : Peano.le x y.
Proof. exact (@lem153125 x y h2 (@lem153116 x y n h1 h2 h3 h4)). Qed.
Lemma lem153129 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : term176 x y.
Proof. exact (fun h0 : term54 x y => @lem153128 x y n h1 h2 h3 h4). Qed.
Lemma lem153131 (p : Prop) : (term152 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem153132 (x : nat) (y : nat) : (term176 x y) = (Peano.le x y).
Proof. exact (@lem153131 (Peano.le x y)). Qed.
Lemma lem153133 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : Peano.le x y.
Proof. exact (EQ_MP (@lem153132 x y) (@lem153129 x y n h1 h2 h3 h4)). Qed.
Lemma lem153136 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem153138 (x : nat) (y : nat) : (term54 x y) = (term177 x y).
Proof. exact (@lem153136 (Peano.le x y)). Qed.
Lemma lem153141 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) : term177 x y.
Proof. exact (EQ_MP (@lem153138 x y) (@lem152961 x y n h1)). Qed.
Lemma lem153144 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : False.
Proof. exact (@lem153141 x y n h3 (@lem153133 x y n h1 h2 h3 h4)). Qed.
Lemma lem153145 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : term178.
Proof. exact (fun h0 : ~ False => @lem153144 x y n h1 h2 h3 h4). Qed.
Lemma lem153147 (p : Prop) : (term152 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem153148 : term178 = False.
Proof. exact (@lem153147 False). Qed.
Lemma lem153149 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : False.
Proof. exact (EQ_MP (@lem153148) (@lem153145 x y n h1 h2 h3 h4)). Qed.
Lemma lem153150 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : (term7 x y n) = False.
Proof. exact (prop_ext (fun h5 : term7 x y n => @lem153149 x y n h1 h2 h3 h4) (fun h5 : False => @lem152935 x y n h4)). Qed.
Lemma lem153151 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : False.
Proof. exact (EQ_MP (@lem153150 x y n h1 h2 h3 h4) (@lem152935 x y n h4)). Qed.
Lemma lem153152 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : (term7 x y n) = False.
Proof. exact (prop_ext (fun h5 : term7 x y n => @lem153151 x y n h1 h2 h3 h4) (fun h5 : False => @lem152847 x y n h4)). Qed.
Lemma lem153153 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : False.
Proof. exact (EQ_MP (@lem153152 x y n h1 h2 h3 h4) (@lem152847 x y n h4)). Qed.
Lemma lem153154 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : (term7 x y n) = False.
Proof. exact (prop_ext (fun h5 : term7 x y n => @lem153153 x y n h1 h2 h3 h4) (fun h5 : False => @lem152847 x y n h4)). Qed.
Lemma lem153155 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : False.
Proof. exact (EQ_MP (@lem153154 x y n h1 h2 h3 h4) (@lem152847 x y n h4)). Qed.
Lemma lem153156 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : (term7 x y n) = False.
Proof. exact (prop_ext (fun h5 : term7 x y n => @lem153155 x y n h1 h2 h3 h4) (fun h5 : False => @lem152730 x y n h4)). Qed.
Lemma lem153157 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : False.
Proof. exact (EQ_MP (@lem153156 x y n h1 h2 h3 h4) (@lem152730 x y n h4)). Qed.
Lemma lem153158 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : (term7 x y n) = False.
Proof. exact (prop_ext (fun h5 : term7 x y n => @lem153157 x y n h1 h2 h3 h4) (fun h5 : False => @lem152330 x y n h4)). Qed.
Lemma lem153159 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term33) (h3 : term26 x y n) (h4 : term7 x y n) : False.
Proof. exact (EQ_MP (@lem153158 x y n h1 h2 h3 h4) (@lem152330 x y n h4)). Qed.
Lemma lem153160 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term26 x y n) (h3 : term7 x y n) : term31.
Proof. exact (fun h0 : term33 => @lem153159 x y n h1 h0 h2 h3). Qed.
Lemma lem153161 : term31 = term32.
Proof. exact (@lem69 term33). Qed.
Lemma lem153162 (x : nat) (y : nat) (n : nat) (h1 : term64) (h2 : term26 x y n) (h3 : term7 x y n) : term32.
Proof. exact (EQ_MP (@lem153161) (@lem153160 x y n h1 h2 h3)). Qed.
Lemma lem153163 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) (h2 : term7 x y n) : term36.
Proof. exact (fun h0 : term64 => @lem153162 x y n h0 h1 h2). Qed.
Lemma lem153164 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : term39 x y n.
Proof. exact (fun h0 : term26 x y n => @lem153163 x y n h0 h1). Qed.
Lemma lem153165 (x : nat) (y : nat) (n : nat) : term41 x y n.
Proof. exact (fun h0 : term7 x y n => @lem153164 x y n h0). Qed.
Lemma lem153170 (y : nat) (n : nat) : term45 y n.
Proof. exact (fun x : nat => @lem153165 x y n). Qed.
Lemma lem153175 (n : nat) : term49 n.
Proof. exact (fun y : nat => @lem153170 y n). Qed.
Lemma lem153180 : term53.
Proof. exact (fun n : nat => @lem153175 n). Qed.
Lemma lem153181 : term52.
Proof. exact (EQ_MP (@lem152320) (@lem153180)). Qed.
Lemma lem153182 (n : nat) : term179 n.
Proof. exact (@lem153181 n). Qed.
Lemma lem153183 (n : nat) : (term179 n) = (term48 n).
Proof. exact (eq_refl (term179 n)). Qed.
Lemma lem153184 (n : nat) : term48 n.
Proof. exact (EQ_MP (@lem153183 n) (@lem153182 n)). Qed.
Lemma lem153185 (n : nat) (y : nat) : term180 n y.
Proof. exact (@lem153184 n y). Qed.
Lemma lem153186 (y : nat) (n : nat) : (term180 n y) = (term44 y n).
Proof. exact (eq_refl (term180 n y)). Qed.
Lemma lem153187 (y : nat) (n : nat) : term44 y n.
Proof. exact (EQ_MP (@lem153186 y n) (@lem153185 n y)). Qed.
Lemma lem153188 (y : nat) (n : nat) (x : nat) : term181 y n x.
Proof. exact (@lem153187 y n x). Qed.
Lemma lem153189 (x : nat) (y : nat) (n : nat) : (term181 y n x) = (term27 x y n).
Proof. exact (eq_refl (term181 y n x)). Qed.
Lemma lem153190 (x : nat) (y : nat) (n : nat) : term27 x y n.
Proof. exact (EQ_MP (@lem153189 x y n) (@lem153188 y n x)). Qed.
Lemma lem153192 (x : nat) (y : nat) (n : nat) : term27 x y n.
Proof. exact (@lem152111 x y n (@lem153190 x y n)). Qed.
Lemma lem153193 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : term38 x y n.
Proof. exact (@lem153192 x y n (@lem151932 x y n h1)). Qed.
Lemma lem153194 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) (h2 : term7 x y n) : term35.
Proof. exact (@lem153193 x y n h2 (@lem152096 x y n h1)). Qed.
Lemma lem153195 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) (h2 : term7 x y n) : term31.
Proof. exact (@lem153194 x y n h1 h2 (@lem151921)). Qed.
Lemma lem153196 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) (h2 : term7 x y n) : False.
Proof. exact (@lem153195 x y n h1 h2 (@lem97961)). Qed.
Lemma lem153197 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) (h2 : term7 x y n) : (term26 x y n) = False.
Proof. exact (prop_ext (fun h3 : term26 x y n => @lem153196 x y n h1 h2) (fun h3 : False => @lem152096 x y n h1)). Qed.
Lemma lem153198 (x : nat) (y : nat) (n : nat) (h1 : term26 x y n) (h2 : term7 x y n) : False.
Proof. exact (EQ_MP (@lem153197 x y n h1 h2) (@lem152096 x y n h1)). Qed.
Lemma lem153199 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : term25 x y n.
Proof. exact (fun h0 : term26 x y n => @lem153198 x y n h0 h1). Qed.
Lemma lem153201 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : term8 x y n.
Proof. exact (EQ_MP (@lem152095 x y n) (@lem153199 x y n h1)). Qed.
Lemma lem153202 (x : nat) (y : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = (term7 x y n).
Proof. exact (prop_ext (fun h2 : n = (NUMERAL 0) => @lem152091 x y n h1) (fun h2 : term7 x y n => @lem151935 n h1)). Qed.
Lemma lem153203 (x : nat) (y : nat) (n : nat) (h1 : n = (NUMERAL 0)) : term7 x y n.
Proof. exact (EQ_MP (@lem153202 x y n h1) (@lem151935 n h1)). Qed.
Lemma lem153204 (n : nat) (x : nat) (y : nat) (h1 : Peano.le x y) : (Peano.le x y) = (term7 x y n).
Proof. exact (prop_ext (fun h2 : Peano.le x y => @lem152024 n x y h1) (fun h2 : term7 x y n => @lem151934 x y h1)). Qed.
Lemma lem153205 (n : nat) (x : nat) (y : nat) (h1 : Peano.le x y) : term7 x y n.
Proof. exact (EQ_MP (@lem153204 n x y h1) (@lem151934 x y h1)). Qed.
Lemma lem153206 (x : nat) (y : nat) (n : nat) (h1 : term8 x y n) : term7 x y n.
Proof. exact (or_elim (@lem151933 x y n h1) (fun h0 : Peano.le x y => @lem153205 n x y h0) (fun h0 : n = (NUMERAL 0) => @lem153203 x y n h0)). Qed.
Lemma lem153207 (x : nat) (y : nat) (n : nat) : term182 x y n.
Proof. exact (fun h0 : term8 x y n => @lem153206 x y n h0). Qed.
Lemma lem153208 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : (term7 x y n) = (term8 x y n).
Proof. exact (prop_ext (fun h2 : term7 x y n => @lem153201 x y n h1) (fun h2 : term8 x y n => @lem151932 x y n h1)). Qed.
Lemma lem153209 (x : nat) (y : nat) (n : nat) (h1 : term7 x y n) : term8 x y n.
Proof. exact (EQ_MP (@lem153208 x y n h1) (@lem151932 x y n h1)). Qed.
Lemma lem153210 (x : nat) (y : nat) (n : nat) : term183 x y n.
Proof. exact (fun h0 : term7 x y n => @lem153209 x y n h0). Qed.
Lemma lem153211 (x : nat) (y : nat) (n : nat) : term184 x y n.
Proof. exact (conj (@lem153210 x y n) (@lem153207 x y n)). Qed.
Lemma lem153212 (x : nat) (y : nat) (n : nat) : (term184 x y n) = ((term7 x y n) = (term8 x y n)).
Proof. exact (@lem32 (term7 x y n) (term8 x y n)). Qed.
Lemma lem153213 (x : nat) (y : nat) (n : nat) : (term7 x y n) = (term8 x y n).
Proof. exact (EQ_MP (@lem153212 x y n) (@lem153211 x y n)). Qed.
Lemma lem153218 (x : nat) (y : nat) : term185 x y.
Proof. exact (fun n : nat => @lem153213 x y n). Qed.
Lemma lem153223 (x : nat) : term186 x.
Proof. exact (fun y : nat => @lem153218 x y). Qed.
Lemma lem153228 : term187.
Proof. exact (fun x : nat => @lem153223 x). Qed.
