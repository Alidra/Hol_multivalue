Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_INT_MEASURE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INT_FORALL_POS_spec.
Require Import INT_OF_NUM_LT_spec.
Require Import num_WF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
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
Require Import thm21386_spec.
Lemma lem2747043 (m : nat) (n : nat) (h1 : (term0 m n) = (Peano.lt m n)) : (term0 m n) = (Peano.lt m n).
Proof. exact (h1). Qed.
Lemma lem2747044 (m : nat) (n : nat) (h1 : (term0 m n) = (Peano.lt m n)) : (Peano.lt m n) = (term0 m n).
Proof. exact (SYM (@lem2747043 m n h1)). Qed.
Lemma lem2747045 (m : nat) (n : nat) (h1 : (Peano.lt m n) = (term0 m n)) : (Peano.lt m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem2747046 (m : nat) (n : nat) (h1 : (Peano.lt m n) = (term0 m n)) : (term0 m n) = (Peano.lt m n).
Proof. exact (SYM (@lem2747045 m n h1)). Qed.
Lemma lem2747047 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt m n)) = ((Peano.lt m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt m n) => @lem2747044 m n h1) (fun h1 : (Peano.lt m n) = (term0 m n) => @lem2747046 m n h1)). Qed.
Lemma lem2747048 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem2747047 m n)). Qed.
Lemma lem2747049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2747050 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem2747049) (@lem2747048 m)). Qed.
Lemma lem2747051 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem2747050 m)). Qed.
Lemma lem2747052 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2747053 : term7 = term8.
Proof. exact (MK_COMB (@lem2747052) (@lem2747051)). Qed.
Lemma lem2747054 : term8.
Proof. exact (EQ_MP (@lem2747053) (@lem2307247)). Qed.
Lemma lem2747055 (P : int -> Prop) : term9 P.
Proof. exact (@lem2315380 P). Qed.
Lemma lem2747056 (P : int -> Prop) : (term9 P) = ((term10 P) = (term11 P)).
Proof. exact (eq_refl (term9 P)). Qed.
Lemma lem2747058 (m : nat) : term12 m.
Proof. exact (@lem2747054 m). Qed.
Lemma lem2747059 (m : nat) : (term12 m) = (term4 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem2747060 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem2747059 m) (@lem2747058 m)). Qed.
Lemma lem2747061 (m : nat) (n : nat) : term13 m n.
Proof. exact (@lem2747060 m n). Qed.
Lemma lem2747062 (m : nat) (n : nat) : (term13 m n) = ((Peano.lt m n) = (term0 m n)).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem2747064 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem2747065 (P : nat -> Prop) (h1 : term14) : term15 P.
Proof. exact (@lem2747064 h1 P). Qed.
Lemma lem2747066 (P : nat -> Prop) : (term15 P) = (term16 P).
Proof. exact (eq_refl (term15 P)). Qed.
Lemma lem2747067 (P : nat -> Prop) (h1 : term14) : term16 P.
Proof. exact (EQ_MP (@lem2747066 P) (@lem2747065 P h1)). Qed.
Lemma lem2747068 (P : nat -> Prop) (h1 : term17 P) : term17 P.
Proof. exact (h1). Qed.
Lemma lem2747069 (P : nat -> Prop) (h1 : term14) (h2 : term17 P) : term18 P.
Proof. exact (@lem2747067 P h1 (@lem2747068 P h2)). Qed.
Lemma lem2747070 (P : nat -> Prop) (h1 : term17 P) : term19 P.
Proof. exact (fun h0 : term14 => @lem2747069 P h0 h1). Qed.
Lemma lem2747071 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem2747072 (P : nat -> Prop) (h1 : term14) (h2 : term17 P) : term18 P.
Proof. exact (@lem2747070 P h2 (@lem2747071 h1)). Qed.
Lemma lem2747073 (P : nat -> Prop) (h1 : term14) : term16 P.
Proof. exact (fun h0 : term17 P => @lem2747072 P h1 h0). Qed.
Lemma lem2747074 (h1 : term14) : term14.
Proof. exact (fun P : nat -> Prop => @lem2747073 P h1). Qed.
Lemma lem2747075 : term20.
Proof. exact (fun h0 : term14 => @lem2747074 h0). Qed.
Lemma lem2747076 : term14.
Proof. exact (@lem2747075 (@lem115780)). Qed.
Lemma lem2747077 (P : nat -> Prop) : term15 P.
Proof. exact (@lem2747076 P). Qed.
Lemma lem2747078 (P : nat -> Prop) : (term15 P) = (term16 P).
Proof. exact (eq_refl (term15 P)). Qed.
Lemma lem2747080 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term21 A m P) : term21 A m P.
Proof. exact (h1). Qed.
Lemma lem2747081 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term22 A m P) : term22 A m P.
Proof. exact (h1). Qed.
Lemma lem2747082 {A : Type'} (m : A -> int) (h1 : term23 A m) : term23 A m.
Proof. exact (h1). Qed.
Lemma lem2747083 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term24 A m P) : term24 A m P.
Proof. exact (h1). Qed.
Lemma lem2747085 (P : nat -> Prop) : term16 P.
Proof. exact (EQ_MP (@lem2747078 P) (@lem2747077 P)). Qed.
Lemma lem2747086 {A : Type'} (m : A -> int) (P : A -> Prop) : term25 A m P.
Proof. exact (@lem2747085 (term26 A m P)). Qed.
Lemma lem2747087 {A : Type'} (m : A -> int) (m' : nat) (P : A -> Prop) : (term27 A m P m') = (term28 A m m' P).
Proof. exact (eq_refl (term27 A m P m')). Qed.
Lemma lem2747088 (m : nat) (n : nat) : (term29 m n) = (term29 m n).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem2747089 {A : Type'} (n : nat) (m : A -> int) (m' : nat) (P : A -> Prop) : (term30 A n m P m') = (term31 A n m m' P).
Proof. exact (MK_COMB (@lem2747088 m' n) (@lem2747087 A m m' P)). Qed.
Lemma lem2747090 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term32 A n m P) = (term33 A n m P).
Proof. exact (fun_ext (fun m' : nat => @lem2747089 A n m m' P)). Qed.
Lemma lem2747091 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2747092 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term34 A n m P) = (term35 A n m P).
Proof. exact (MK_COMB (@lem2747091) (@lem2747090 A n m P)). Qed.
Lemma lem2747093 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2747094 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term36 A n m P) = (term37 A n m P).
Proof. exact (MK_COMB (@lem2747093) (@lem2747092 A n m P)). Qed.
Lemma lem2747095 {A : Type'} (m : A -> int) (n : nat) (P : A -> Prop) : (term27 A m P n) = (term28 A m n P).
Proof. exact (eq_refl (term27 A m P n)). Qed.
Lemma lem2747096 {A : Type'} (m : A -> int) (n : nat) (P : A -> Prop) : (term38 A m P n) = (term39 A m n P).
Proof. exact (MK_COMB (@lem2747094 A n m P) (@lem2747095 A m n P)). Qed.
Lemma lem2747097 {A : Type'} (m : A -> int) (P : A -> Prop) : (term40 A m P) = (term41 A m P).
Proof. exact (fun_ext (fun n : nat => @lem2747096 A m n P)). Qed.
Lemma lem2747098 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2747099 {A : Type'} (m : A -> int) (P : A -> Prop) : (term42 A m P) = (term43 A m P).
Proof. exact (MK_COMB (@lem2747098) (@lem2747097 A m P)). Qed.
Lemma lem2747100 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2747101 {A : Type'} (m : A -> int) (P : A -> Prop) : (term44 A m P) = (term45 A m P).
Proof. exact (MK_COMB (@lem2747100) (@lem2747099 A m P)). Qed.
Lemma lem2747102 {A : Type'} (m : A -> int) (n : nat) (P : A -> Prop) : (term27 A m P n) = (term28 A m n P).
Proof. exact (eq_refl (term27 A m P n)). Qed.
Lemma lem2747103 {A : Type'} (m : A -> int) (P : A -> Prop) : (term46 A m P) = (term26 A m P).
Proof. exact (fun_ext (fun n : nat => @lem2747102 A m n P)). Qed.
Lemma lem2747104 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2747105 {A : Type'} (m : A -> int) (P : A -> Prop) : (term47 A m P) = (term24 A m P).
Proof. exact (MK_COMB (@lem2747104) (@lem2747103 A m P)). Qed.
Lemma lem2747106 {A : Type'} (m : A -> int) (P : A -> Prop) : (term25 A m P) = (term48 A m P).
Proof. exact (MK_COMB (@lem2747101 A m P) (@lem2747105 A m P)). Qed.
Lemma lem2747107 {A : Type'} (m : A -> int) (P : A -> Prop) : term48 A m P.
Proof. exact (EQ_MP (@lem2747106 A m P) (@lem2747086 A m P)). Qed.
Lemma lem2747155 (m : nat) (n : nat) : (Peano.lt m n) = (term0 m n).
Proof. exact (EQ_MP (@lem2747062 m n) (@lem2747061 m n)). Qed.
Lemma lem2747156 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2747157 (m : nat) (n : nat) : (term29 m n) = (term49 m n).
Proof. exact (MK_COMB (@lem2747156) (@lem2747155 m n)). Qed.
Lemma lem2747170 {A : Type'} (m : A -> int) (m' : nat) (P : A -> Prop) : (term28 A m m' P) = (term28 A m m' P).
Proof. exact (eq_refl (term28 A m m' P)). Qed.
Lemma lem2747171 {A : Type'} (n : nat) (m : A -> int) (m' : nat) (P : A -> Prop) : (term31 A n m m' P) = (term50 A n m m' P).
Proof. exact (MK_COMB (@lem2747157 m' n) (@lem2747170 A m m' P)). Qed.
Lemma lem2747174 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term33 A n m P) = (term51 A n m P).
Proof. exact (fun_ext (fun m' : nat => @lem2747171 A n m m' P)). Qed.
Lemma lem2747175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2747176 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term35 A n m P) = (term52 A n m P).
Proof. exact (MK_COMB (@lem2747175) (@lem2747174 A n m P)). Qed.
Lemma lem2747182 (P : int -> Prop) : (term10 P) = (term11 P).
Proof. exact (EQ_MP (@lem2747056 P) (@lem2747055 P)). Qed.
Lemma lem2747183 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term53 A n m P) = (term54 A n m P).
Proof. exact (@lem2747182 (term55 A n m P)). Qed.
Lemma lem2747184 {A : Type'} (n : nat) (m : A -> int) (m' : nat) (P : A -> Prop) : (term56 A n m P m') = (term50 A n m m' P).
Proof. exact (eq_refl (term56 A n m P m')). Qed.
Lemma lem2747185 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term57 A n m P) = (term51 A n m P).
Proof. exact (fun_ext (fun m' : nat => @lem2747184 A n m m' P)). Qed.
Lemma lem2747186 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2747187 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term53 A n m P) = (term52 A n m P).
Proof. exact (MK_COMB (@lem2747186) (@lem2747185 A n m P)). Qed.
Lemma lem2747188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2747189 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term58 A n m P) = (term59 A n m P).
Proof. exact (MK_COMB (@lem2747188) (@lem2747187 A n m P)). Qed.
Lemma lem2747190 {A : Type'} (n : nat) (m : A -> int) (i : int) (P : A -> Prop) : (term60 A n m P i) = (term61 A n m i P).
Proof. exact (eq_refl (term60 A n m P i)). Qed.
Lemma lem2747191 (i : int) : (term62 i) = (term62 i).
Proof. exact (eq_refl (term62 i)). Qed.
Lemma lem2747192 {A : Type'} (n : nat) (m : A -> int) (i : int) (P : A -> Prop) : (term63 A n m P i) = (term64 A n m i P).
Proof. exact (MK_COMB (@lem2747191 i) (@lem2747190 A n m i P)). Qed.
Lemma lem2747193 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term65 A n m P) = (term66 A n m P).
Proof. exact (fun_ext (fun i : int => @lem2747192 A n m i P)). Qed.
Lemma lem2747194 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2747195 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term54 A n m P) = (term67 A n m P).
Proof. exact (MK_COMB (@lem2747194) (@lem2747193 A n m P)). Qed.
Lemma lem2747196 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : ((term53 A n m P) = (term54 A n m P)) = ((term52 A n m P) = (term67 A n m P)).
Proof. exact (MK_COMB (@lem2747189 A n m P) (@lem2747195 A n m P)). Qed.
Lemma lem2747197 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term52 A n m P) = (term67 A n m P).
Proof. exact (EQ_MP (@lem2747196 A n m P) (@lem2747183 A n m P)). Qed.
Lemma lem2747220 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term35 A n m P) = (term67 A n m P).
Proof. exact (TRANS (@lem2747176 A n m P) (@lem2747197 A n m P)). Qed.
Lemma lem2747221 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2747222 {A : Type'} (n : nat) (m : A -> int) (P : A -> Prop) : (term37 A n m P) = (term68 A n m P).
Proof. exact (MK_COMB (@lem2747221) (@lem2747220 A n m P)). Qed.
Lemma lem2747235 {A : Type'} (m : A -> int) (n : nat) (P : A -> Prop) : (term28 A m n P) = (term28 A m n P).
Proof. exact (eq_refl (term28 A m n P)). Qed.
Lemma lem2747236 {A : Type'} (m : A -> int) (n : nat) (P : A -> Prop) : (term39 A m n P) = (term69 A m n P).
Proof. exact (MK_COMB (@lem2747222 A n m P) (@lem2747235 A m n P)). Qed.
Lemma lem2747239 {A : Type'} (m : A -> int) (P : A -> Prop) : (term41 A m P) = (term70 A m P).
Proof. exact (fun_ext (fun n : nat => @lem2747236 A m n P)). Qed.
Lemma lem2747240 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2747241 {A : Type'} (m : A -> int) (P : A -> Prop) : (term43 A m P) = (term71 A m P).
Proof. exact (MK_COMB (@lem2747240) (@lem2747239 A m P)). Qed.
Lemma lem2747247 (P : int -> Prop) : (term10 P) = (term11 P).
Proof. exact (EQ_MP (@lem2747056 P) (@lem2747055 P)). Qed.
Lemma lem2747248 {A : Type'} (m : A -> int) (P : A -> Prop) : (term72 A m P) = (term73 A m P).
Proof. exact (@lem2747247 (term74 A m P)). Qed.
Lemma lem2747249 {A : Type'} (m : A -> int) (n : nat) (P : A -> Prop) : (term75 A m P n) = (term69 A m n P).
Proof. exact (eq_refl (term75 A m P n)). Qed.
Lemma lem2747250 {A : Type'} (m : A -> int) (P : A -> Prop) : (term76 A m P) = (term70 A m P).
Proof. exact (fun_ext (fun n : nat => @lem2747249 A m n P)). Qed.
Lemma lem2747251 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2747252 {A : Type'} (m : A -> int) (P : A -> Prop) : (term72 A m P) = (term71 A m P).
Proof. exact (MK_COMB (@lem2747251) (@lem2747250 A m P)). Qed.
Lemma lem2747253 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2747254 {A : Type'} (m : A -> int) (P : A -> Prop) : (term77 A m P) = (term78 A m P).
Proof. exact (MK_COMB (@lem2747253) (@lem2747252 A m P)). Qed.
Lemma lem2747255 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term79 A m P i) = (term80 A m i P).
Proof. exact (eq_refl (term79 A m P i)). Qed.
Lemma lem2747256 (i : int) : (term62 i) = (term62 i).
Proof. exact (eq_refl (term62 i)). Qed.
Lemma lem2747257 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term81 A m P i) = (term82 A m i P).
Proof. exact (MK_COMB (@lem2747256 i) (@lem2747255 A m i P)). Qed.
Lemma lem2747258 {A : Type'} (m : A -> int) (P : A -> Prop) : (term83 A m P) = (term84 A m P).
Proof. exact (fun_ext (fun i : int => @lem2747257 A m i P)). Qed.
Lemma lem2747259 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2747260 {A : Type'} (m : A -> int) (P : A -> Prop) : (term73 A m P) = (term85 A m P).
Proof. exact (MK_COMB (@lem2747259) (@lem2747258 A m P)). Qed.
Lemma lem2747261 {A : Type'} (m : A -> int) (P : A -> Prop) : ((term72 A m P) = (term73 A m P)) = ((term71 A m P) = (term85 A m P)).
Proof. exact (MK_COMB (@lem2747254 A m P) (@lem2747260 A m P)). Qed.
Lemma lem2747262 {A : Type'} (m : A -> int) (P : A -> Prop) : (term71 A m P) = (term85 A m P).
Proof. exact (EQ_MP (@lem2747261 A m P) (@lem2747248 A m P)). Qed.
Lemma lem2747307 {A : Type'} (m : A -> int) (P : A -> Prop) : (term43 A m P) = (term85 A m P).
Proof. exact (TRANS (@lem2747241 A m P) (@lem2747262 A m P)). Qed.
Lemma lem2747308 {A : Type'} (m : A -> int) (P : A -> Prop) : (term85 A m P) = (term43 A m P).
Proof. exact (SYM (@lem2747307 A m P)). Qed.
Lemma lem2747316 (P : int -> Prop) : (term10 P) = (term11 P).
Proof. exact (EQ_MP (@lem2747056 P) (@lem2747055 P)). Qed.
Lemma lem2747317 {A : Type'} (m : A -> int) (P : A -> Prop) : (term86 A m P) = (term87 A m P).
Proof. exact (@lem2747316 (term88 A m P)). Qed.
Lemma lem2747318 {A : Type'} (m : A -> int) (n : nat) (P : A -> Prop) : (term89 A m P n) = (term28 A m n P).
Proof. exact (eq_refl (term89 A m P n)). Qed.
Lemma lem2747319 {A : Type'} (m : A -> int) (P : A -> Prop) : (term90 A m P) = (term26 A m P).
Proof. exact (fun_ext (fun n : nat => @lem2747318 A m n P)). Qed.
Lemma lem2747320 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2747321 {A : Type'} (m : A -> int) (P : A -> Prop) : (term86 A m P) = (term24 A m P).
Proof. exact (MK_COMB (@lem2747320) (@lem2747319 A m P)). Qed.
Lemma lem2747322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2747323 {A : Type'} (m : A -> int) (P : A -> Prop) : (term91 A m P) = (term92 A m P).
Proof. exact (MK_COMB (@lem2747322) (@lem2747321 A m P)). Qed.
Lemma lem2747324 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term93 A m P i) = (term94 A m i P).
Proof. exact (eq_refl (term93 A m P i)). Qed.
Lemma lem2747325 (i : int) : (term62 i) = (term62 i).
Proof. exact (eq_refl (term62 i)). Qed.
Lemma lem2747326 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term95 A m P i) = (term96 A m i P).
Proof. exact (MK_COMB (@lem2747325 i) (@lem2747324 A m i P)). Qed.
Lemma lem2747327 {A : Type'} (m : A -> int) (P : A -> Prop) : (term97 A m P) = (term98 A m P).
Proof. exact (fun_ext (fun i : int => @lem2747326 A m i P)). Qed.
Lemma lem2747328 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2747329 {A : Type'} (m : A -> int) (P : A -> Prop) : (term87 A m P) = (term99 A m P).
Proof. exact (MK_COMB (@lem2747328) (@lem2747327 A m P)). Qed.
Lemma lem2747330 {A : Type'} (m : A -> int) (P : A -> Prop) : ((term86 A m P) = (term87 A m P)) = ((term24 A m P) = (term99 A m P)).
Proof. exact (MK_COMB (@lem2747323 A m P) (@lem2747329 A m P)). Qed.
Lemma lem2747331 {A : Type'} (m : A -> int) (P : A -> Prop) : (term24 A m P) = (term99 A m P).
Proof. exact (EQ_MP (@lem2747330 A m P) (@lem2747317 A m P)). Qed.
Lemma lem2747352 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2747353 {A : Type'} (m : A -> int) (P : A -> Prop) : (term100 A m P) = (term101 A m P).
Proof. exact (MK_COMB (@lem2747352) (@lem2747331 A m P)). Qed.
Lemma lem2747354 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2747355 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term102 A m P x) = (term103 A m P x).
Proof. exact (MK_COMB (@lem2747353 A m P) (@lem2747354 A P x)). Qed.
Lemma lem2747358 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term103 A m P x) = (term102 A m P x).
Proof. exact (SYM (@lem2747355 A m P x)). Qed.
Lemma lem2747360 (p : Prop) : p = (term104 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2747361 {A : Type'} (m : A -> int) (P : A -> Prop) : (term85 A m P) = (term105 A m P).
Proof. exact (@lem2747360 (term85 A m P)). Qed.
Lemma lem2747362 {A : Type'} (m : A -> int) (P : A -> Prop) : (term105 A m P) = (term85 A m P).
Proof. exact (SYM (@lem2747361 A m P)). Qed.
Lemma lem2747363 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term106 A m P) : term106 A m P.
Proof. exact (h1). Qed.
Lemma lem2747366 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term107 A m P) : term107 A m P.
Proof. exact (h1). Qed.
Lemma lem2747367 {A : Type'} (m : A -> int) (P : A -> Prop) : term108 A m P.
Proof. exact (fun h0 : term107 A m P => @lem2747366 A m P h0). Qed.
Lemma lem2747368 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term108 A m P) : term108 A m P.
Proof. exact (h1). Qed.
Lemma lem2747369 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term107 A m P) : term107 A m P.
Proof. exact (h1). Qed.
Lemma lem2747370 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term107 A m P) (h2 : term108 A m P) : term107 A m P.
Proof. exact (@lem2747368 A m P h2 (@lem2747369 A m P h1)). Qed.
Lemma lem2747371 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term107 A m P) : term109 A m P.
Proof. exact (fun h0 : term108 A m P => @lem2747370 A m P h1 h0). Qed.
Lemma lem2747372 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term108 A m P) : term108 A m P.
Proof. exact (h1). Qed.
Lemma lem2747373 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term107 A m P) (h2 : term108 A m P) : term107 A m P.
Proof. exact (@lem2747371 A m P h1 (@lem2747372 A m P h2)). Qed.
Lemma lem2747374 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term108 A m P) : term108 A m P.
Proof. exact (fun h0 : term107 A m P => @lem2747373 A m P h0 h1). Qed.
Lemma lem2747375 {A : Type'} (m : A -> int) (P : A -> Prop) : term110 A m P.
Proof. exact (fun h0 : term108 A m P => @lem2747374 A m P h0). Qed.
Lemma lem2747378 {A : Type'} (m : A -> int) (P : A -> Prop) : term108 A m P.
Proof. exact (@lem2747375 A m P (@lem2747367 A m P)). Qed.
Lemma lem2747379 {A : Type'} (m : A -> int) (P : A -> Prop) : term108 A m P.
Proof. exact (@lem2747378 A m P). Qed.
Lemma lem2747409 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2747410 {A : Type'} (m : A -> int) (P : A -> Prop) : (term105 A m P) = (term111 A m P).
Proof. exact (@lem2747409 (term106 A m P)). Qed.
Lemma lem2747412 (t : Prop) : (term112 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2747413 {A : Type'} (m : A -> int) (P : A -> Prop) : (term111 A m P) = (term85 A m P).
Proof. exact (@lem2747412 (term85 A m P)). Qed.
Lemma lem2747418 {A : Type'} (m : A -> int) (P : A -> Prop) : (term105 A m P) = (term85 A m P).
Proof. exact (TRANS (@lem2747410 A m P) (@lem2747413 A m P)). Qed.
Lemma lem2747443 {A : Type'} (m : A -> int) (P : A -> Prop) : (term113 A m P) = (term113 A m P).
Proof. exact (eq_refl (term113 A m P)). Qed.
Lemma lem2747444 {A : Type'} (m : A -> int) (P : A -> Prop) : (term114 A m P) = (term115 A m P).
Proof. exact (MK_COMB (@lem2747443 A m P) (@lem2747418 A m P)). Qed.
Lemma lem2747447 {A : Type'} (m : A -> int) : (term116 A m) = (term116 A m).
Proof. exact (eq_refl (term116 A m)). Qed.
Lemma lem2747448 {A : Type'} (m : A -> int) (P : A -> Prop) : (term107 A m P) = (term117 A m P).
Proof. exact (MK_COMB (@lem2747447 A m) (@lem2747444 A m P)). Qed.
Lemma lem2747451 {A : Type'} (P : A -> Prop) : (term118 A P) = (term119 A P).
Proof. exact (fun_ext (fun m : A -> int => @lem2747448 A m P)). Qed.
Lemma lem2747452 {A : Type'} : (@all (A -> int)) = (@all (A -> int)).
Proof. exact (eq_refl (@all (A -> int))). Qed.
Lemma lem2747453 {A : Type'} (P : A -> Prop) : (term120 A P) = (term121 A P).
Proof. exact (MK_COMB (@lem2747452 A) (@lem2747451 A P)). Qed.
Lemma lem2747458 {A : Type'} : (term122 A) = (term123 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem2747453 A P)). Qed.
Lemma lem2747459 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem2747468 {A : Type'} : (term124 A) = (term125 A).
Proof. exact (MK_COMB (@lem2747459 A) (@lem2747458 A)). Qed.
Lemma lem2747473 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) (x : A) : (term126 A m i P x) = (term126 A m i P x).
Proof. exact (eq_refl (term126 A m i P x)). Qed.
Lemma lem2747474 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term127 A m i P) = (term127 A m i P).
Proof. exact (fun_ext (fun x : A => @lem2747473 A m i P x)). Qed.
Lemma lem2747475 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2747476 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term94 A m i P) = (term94 A m i P).
Proof. exact (MK_COMB (@lem2747475 A) (@lem2747474 A m i P)). Qed.
Lemma lem2747481 {A : Type'} (m : A -> int) (i' : int) (P : A -> Prop) (x : A) : (term126 A m i' P x) = (term126 A m i' P x).
Proof. exact (eq_refl (term126 A m i' P x)). Qed.
Lemma lem2747482 {A : Type'} (m : A -> int) (i' : int) (P : A -> Prop) : (term127 A m i' P) = (term127 A m i' P).
Proof. exact (fun_ext (fun x : A => @lem2747481 A m i' P x)). Qed.
Lemma lem2747483 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2747484 {A : Type'} (m : A -> int) (i' : int) (P : A -> Prop) : (term94 A m i' P) = (term94 A m i' P).
Proof. exact (MK_COMB (@lem2747483 A) (@lem2747482 A m i' P)). Qed.
Lemma lem2747487 (i' : int) (i : int) : (term128 i' i) = (term128 i' i).
Proof. exact (eq_refl (term128 i' i)). Qed.
Lemma lem2747488 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term129 A i m i' P) = (term129 A i m i' P).
Proof. exact (MK_COMB (@lem2747487 i' i) (@lem2747484 A m i' P)). Qed.
Lemma lem2747491 (i' : int) : (term62 i') = (term62 i').
Proof. exact (eq_refl (term62 i')). Qed.
Lemma lem2747492 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term130 A i m i' P) = (term130 A i m i' P).
Proof. exact (MK_COMB (@lem2747491 i') (@lem2747488 A i m i' P)). Qed.
Lemma lem2747493 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) : (term131 A i m P) = (term131 A i m P).
Proof. exact (fun_ext (fun i' : int => @lem2747492 A i m i' P)). Qed.
Lemma lem2747494 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2747495 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) : (term132 A i m P) = (term132 A i m P).
Proof. exact (MK_COMB (@lem2747494) (@lem2747493 A i m P)). Qed.
Lemma lem2747496 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2747497 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) : (term133 A i m P) = (term133 A i m P).
Proof. exact (MK_COMB (@lem2747496) (@lem2747495 A i m P)). Qed.
Lemma lem2747498 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term80 A m i P) = (term80 A m i P).
Proof. exact (MK_COMB (@lem2747497 A i m P) (@lem2747476 A m i P)). Qed.
Lemma lem2747501 (i : int) : (term62 i) = (term62 i).
Proof. exact (eq_refl (term62 i)). Qed.
Lemma lem2747502 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term82 A m i P) = (term82 A m i P).
Proof. exact (MK_COMB (@lem2747501 i) (@lem2747498 A m i P)). Qed.
Lemma lem2747503 {A : Type'} (m : A -> int) (P : A -> Prop) : (term84 A m P) = (term84 A m P).
Proof. exact (fun_ext (fun i : int => @lem2747502 A m i P)). Qed.
Lemma lem2747504 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2747505 {A : Type'} (m : A -> int) (P : A -> Prop) : (term85 A m P) = (term85 A m P).
Proof. exact (MK_COMB (@lem2747504) (@lem2747503 A m P)). Qed.
Lemma lem2747506 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2747511 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term134 A m x P y) = (term134 A m x P y).
Proof. exact (eq_refl (term134 A m x P y)). Qed.
Lemma lem2747512 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term135 A m x P) = (term135 A m x P).
Proof. exact (fun_ext (fun y : A => @lem2747511 A m x P y)). Qed.
Lemma lem2747513 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2747514 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term136 A m x P) = (term136 A m x P).
Proof. exact (MK_COMB (@lem2747513 A) (@lem2747512 A m x P)). Qed.
Lemma lem2747515 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2747516 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term137 A m x P) = (term137 A m x P).
Proof. exact (MK_COMB (@lem2747515) (@lem2747514 A m x P)). Qed.
Lemma lem2747517 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term138 A m P x) = (term138 A m P x).
Proof. exact (MK_COMB (@lem2747516 A m x P) (@lem2747506 A P x)). Qed.
Lemma lem2747518 {A : Type'} (m : A -> int) (P : A -> Prop) : (term139 A m P) = (term139 A m P).
Proof. exact (fun_ext (fun x : A => @lem2747517 A m P x)). Qed.
Lemma lem2747519 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2747520 {A : Type'} (m : A -> int) (P : A -> Prop) : (term22 A m P) = (term22 A m P).
Proof. exact (MK_COMB (@lem2747519 A) (@lem2747518 A m P)). Qed.
Lemma lem2747521 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2747522 {A : Type'} (m : A -> int) (P : A -> Prop) : (term113 A m P) = (term113 A m P).
Proof. exact (MK_COMB (@lem2747521) (@lem2747520 A m P)). Qed.
Lemma lem2747523 {A : Type'} (m : A -> int) (P : A -> Prop) : (term115 A m P) = (term115 A m P).
Proof. exact (MK_COMB (@lem2747522 A m P) (@lem2747505 A m P)). Qed.
Lemma lem2747524 {A : Type'} (m : A -> int) (x : A) : (term140 A m x) = (term140 A m x).
Proof. exact (eq_refl (term140 A m x)). Qed.
Lemma lem2747525 {A : Type'} (m : A -> int) : (term141 A m) = (term141 A m).
Proof. exact (fun_ext (fun x : A => @lem2747524 A m x)). Qed.
Lemma lem2747526 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2747527 {A : Type'} (m : A -> int) : (term23 A m) = (term23 A m).
Proof. exact (MK_COMB (@lem2747526 A) (@lem2747525 A m)). Qed.
Lemma lem2747528 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2747529 {A : Type'} (m : A -> int) : (term116 A m) = (term116 A m).
Proof. exact (MK_COMB (@lem2747528) (@lem2747527 A m)). Qed.
Lemma lem2747530 {A : Type'} (m : A -> int) (P : A -> Prop) : (term117 A m P) = (term117 A m P).
Proof. exact (MK_COMB (@lem2747529 A m) (@lem2747523 A m P)). Qed.
Lemma lem2747531 {A : Type'} (P : A -> Prop) : (term119 A P) = (term119 A P).
Proof. exact (fun_ext (fun m : A -> int => @lem2747530 A m P)). Qed.
Lemma lem2747532 {A : Type'} : (@all (A -> int)) = (@all (A -> int)).
Proof. exact (eq_refl (@all (A -> int))). Qed.
Lemma lem2747533 {A : Type'} (P : A -> Prop) : (term121 A P) = (term121 A P).
Proof. exact (MK_COMB (@lem2747532 A) (@lem2747531 A P)). Qed.
Lemma lem2747534 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem2747533 A P)). Qed.
Lemma lem2747535 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem2747536 {A : Type'} : (term125 A) = (term125 A).
Proof. exact (MK_COMB (@lem2747535 A) (@lem2747534 A)). Qed.
Lemma lem2747613 {A : Type'} : (term124 A) = (term125 A).
Proof. exact (TRANS (@lem2747468 A) (@lem2747536 A)). Qed.
Lemma lem2747614 {A : Type'} : (term125 A) = (term124 A).
Proof. exact (SYM (@lem2747613 A)). Qed.
Lemma lem2747615 {A : Type'} (m : A -> int) (h1 : term23 A m) : term23 A m.
Proof. exact (h1). Qed.
Lemma lem2747616 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term22 A m P) : term22 A m P.
Proof. exact (h1). Qed.
Lemma lem2747618 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) (h1 : term132 A i m P) : term132 A i m P.
Proof. exact (h1). Qed.
Lemma lem2747621 (p : Prop) : p = (term104 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2747622 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (term142 A P x).
Proof. exact (@lem2747621 (P x)). Qed.
Lemma lem2747623 {A : Type'} (P : A -> Prop) (x : A) : (term142 A P x) = (P x).
Proof. exact (SYM (@lem2747622 A P x)). Qed.
Lemma lem2747624 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term143 A P x.
Proof. exact (h1). Qed.
Lemma lem2747625 {A : Type'} (m : A -> int) (x : A) : (term140 A m x) = (term140 A m x).
Proof. exact (eq_refl (term140 A m x)). Qed.
Lemma lem2747626 {A : Type'} (m : A -> int) : (term141 A m) = (term141 A m).
Proof. exact (fun_ext (fun x : A => @lem2747625 A m x)). Qed.
Lemma lem2747627 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2747636 {A : Type'} (m : A -> int) : (term23 A m) = (term23 A m).
Proof. exact (MK_COMB (@lem2747627 A) (@lem2747626 A m)). Qed.
Lemma lem2747637 {A : Type'} (m : A -> int) (h1 : term23 A m) : term23 A m.
Proof. exact (EQ_MP (@lem2747636 A m) (@lem2747615 A m h1)). Qed.
Lemma lem2747644 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term144 A m x P y) = (term145 A m x P y).
Proof. exact (@lem17362 (term146 A y m x) (P y)). Qed.
Lemma lem2747645 {A : Type'} (P : A -> Prop) : (term147 A P) = (term148 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem2747646 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term149 A m x P) = (term150 A m x P).
Proof. exact (@lem2747645 A (term135 A m x P)). Qed.
Lemma lem2747647 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term151 A m x P y) = (term134 A m x P y).
Proof. exact (eq_refl (term151 A m x P y)). Qed.
Lemma lem2747648 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2747649 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term152 A m x P y) = (term144 A m x P y).
Proof. exact (MK_COMB (@lem2747648) (@lem2747647 A m x P y)). Qed.
Lemma lem2747650 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term152 A m x P y) = (term145 A m x P y).
Proof. exact (TRANS (@lem2747649 A m x P y) (@lem2747644 A m x P y)). Qed.
Lemma lem2747651 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term153 A m x P) = (term154 A m x P).
Proof. exact (fun_ext (fun y : A => @lem2747650 A m x P y)). Qed.
Lemma lem2747652 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2747653 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term150 A m x P) = (term155 A m x P).
Proof. exact (MK_COMB (@lem2747652 A) (@lem2747651 A m x P)). Qed.
Lemma lem2747654 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term149 A m x P) = (term155 A m x P).
Proof. exact (TRANS (@lem2747646 A m x P) (@lem2747653 A m x P)). Qed.
Lemma lem2747655 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2747656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2747657 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term156 A m x P) = (term157 A m x P).
Proof. exact (MK_COMB (@lem2747656) (@lem2747654 A m x P)). Qed.
Lemma lem2747658 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term158 A m P x) = (term159 A m P x).
Proof. exact (MK_COMB (@lem2747657 A m x P) (@lem2747655 A P x)). Qed.
Lemma lem2747659 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term138 A m P x) = (term158 A m P x).
Proof. exact (@lem17265 (term136 A m x P) (P x)). Qed.
Lemma lem2747660 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term138 A m P x) = (term159 A m P x).
Proof. exact (TRANS (@lem2747659 A m P x) (@lem2747658 A m P x)). Qed.
Lemma lem2747661 {A : Type'} (m : A -> int) (P : A -> Prop) : (term139 A m P) = (term160 A m P).
Proof. exact (fun_ext (fun x : A => @lem2747660 A m P x)). Qed.
Lemma lem2747662 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2747663 {A : Type'} (m : A -> int) (P : A -> Prop) : (term22 A m P) = (term161 A m P).
Proof. exact (MK_COMB (@lem2747662 A) (@lem2747661 A m P)). Qed.
Lemma lem2747746 {A : Type'} (P : A -> Prop) (Q : Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem2747747 {A : Type'} (P : A -> Prop) (Q : Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (@lem2747746 A P Q). Qed.
Lemma lem2747748 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term164 A m P x) = (term165 A m P x).
Proof. exact (@lem2747747 A (term154 A m x P) (P x)). Qed.
Lemma lem2747749 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term166 A m x P y) = (term145 A m x P y).
Proof. exact (eq_refl (term166 A m x P y)). Qed.
Lemma lem2747750 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term167 A m x P) = (term154 A m x P).
Proof. exact (fun_ext (fun y : A => @lem2747749 A m x P y)). Qed.
Lemma lem2747751 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2747752 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term168 A m x P) = (term155 A m x P).
Proof. exact (MK_COMB (@lem2747751 A) (@lem2747750 A m x P)). Qed.
Lemma lem2747753 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2747754 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term169 A m x P) = (term157 A m x P).
Proof. exact (MK_COMB (@lem2747753) (@lem2747752 A m x P)). Qed.
Lemma lem2747755 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2747756 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term164 A m P x) = (term159 A m P x).
Proof. exact (MK_COMB (@lem2747754 A m x P) (@lem2747755 A P x)). Qed.
Lemma lem2747757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2747758 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term170 A m P x) = (term171 A m P x).
Proof. exact (MK_COMB (@lem2747757) (@lem2747756 A m P x)). Qed.
Lemma lem2747759 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term166 A m x P y) = (term145 A m x P y).
Proof. exact (eq_refl (term166 A m x P y)). Qed.
Lemma lem2747760 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2747761 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term172 A m x P y) = (term173 A m x P y).
Proof. exact (MK_COMB (@lem2747760) (@lem2747759 A m x P y)). Qed.
Lemma lem2747762 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2747763 {A : Type'} (m : A -> int) (y : A) (P : A -> Prop) (x : A) : (term174 A m y P x) = (term175 A m y P x).
Proof. exact (MK_COMB (@lem2747761 A m x P y) (@lem2747762 A P x)). Qed.
Lemma lem2747764 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term176 A m P x) = (term177 A m P x).
Proof. exact (fun_ext (fun y : A => @lem2747763 A m y P x)). Qed.
Lemma lem2747765 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2747766 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term165 A m P x) = (term178 A m P x).
Proof. exact (MK_COMB (@lem2747765 A) (@lem2747764 A m P x)). Qed.
Lemma lem2747767 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : ((term164 A m P x) = (term165 A m P x)) = ((term159 A m P x) = (term178 A m P x)).
Proof. exact (MK_COMB (@lem2747758 A m P x) (@lem2747766 A m P x)). Qed.
Lemma lem2747768 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term159 A m P x) = (term178 A m P x).
Proof. exact (EQ_MP (@lem2747767 A m P x) (@lem2747748 A m P x)). Qed.
Lemma lem2747769 {A : Type'} (m : A -> int) (P : A -> Prop) : (term160 A m P) = (term179 A m P).
Proof. exact (fun_ext (fun x : A => @lem2747768 A m P x)). Qed.
Lemma lem2747770 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2747771 {A : Type'} (m : A -> int) (P : A -> Prop) : (term161 A m P) = (term180 A m P).
Proof. exact (MK_COMB (@lem2747770 A) (@lem2747769 A m P)). Qed.
Lemma lem2747773 {A B : Type'} (P : type1413 A B) : (term181 A B P) = (term182 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem2747774 {A : Type'} (P : type1402 A) : (term183 A P) = (term184 A P).
Proof. exact (@lem2747773 A A P). Qed.
Lemma lem2747775 {A : Type'} (m : A -> int) (P : A -> Prop) : (term185 A m P) = (term186 A m P).
Proof. exact (@lem2747774 A (term187 A m P)). Qed.
Lemma lem2747776 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term188 A m P x) = (term177 A m P x).
Proof. exact (eq_refl (term188 A m P x)). Qed.
Lemma lem2747777 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2747778 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (y : A) : (term189 A m P x y) = (term190 A m P x y).
Proof. exact (MK_COMB (@lem2747776 A m P x) (@lem2747777 A y)). Qed.
Lemma lem2747779 {A : Type'} (m : A -> int) (y : A) (P : A -> Prop) (x : A) : (term190 A m P x y) = (term175 A m y P x).
Proof. exact (eq_refl (term190 A m P x y)). Qed.
Lemma lem2747780 {A : Type'} (m : A -> int) (y : A) (P : A -> Prop) (x : A) : (term189 A m P x y) = (term175 A m y P x).
Proof. exact (TRANS (@lem2747778 A m P x y) (@lem2747779 A m y P x)). Qed.
Lemma lem2747781 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term191 A m P x) = (term177 A m P x).
Proof. exact (fun_ext (fun y : A => @lem2747780 A m y P x)). Qed.
Lemma lem2747782 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2747783 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term192 A m P x) = (term178 A m P x).
Proof. exact (MK_COMB (@lem2747782 A) (@lem2747781 A m P x)). Qed.
Lemma lem2747784 {A : Type'} (m : A -> int) (P : A -> Prop) : (term193 A m P) = (term179 A m P).
Proof. exact (fun_ext (fun x : A => @lem2747783 A m P x)). Qed.
Lemma lem2747785 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2747786 {A : Type'} (m : A -> int) (P : A -> Prop) : (term185 A m P) = (term180 A m P).
Proof. exact (MK_COMB (@lem2747785 A) (@lem2747784 A m P)). Qed.
Lemma lem2747787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2747788 {A : Type'} (m : A -> int) (P : A -> Prop) : (term194 A m P) = (term195 A m P).
Proof. exact (MK_COMB (@lem2747787) (@lem2747786 A m P)). Qed.
Lemma lem2747789 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term188 A m P x) = (term177 A m P x).
Proof. exact (eq_refl (term188 A m P x)). Qed.
Lemma lem2747790 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem2747791 {A : Type'} (m : A -> int) (P : A -> Prop) (y : A -> A) (x : A) : (term196 A m P y x) = (term197 A m P y x).
Proof. exact (MK_COMB (@lem2747789 A m P x) (@lem2747790 A y x)). Qed.
Lemma lem2747792 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (x : A) : (term197 A m P y x) = (term198 A m y P x).
Proof. exact (eq_refl (term197 A m P y x)). Qed.
Lemma lem2747793 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (x : A) : (term196 A m P y x) = (term198 A m y P x).
Proof. exact (TRANS (@lem2747791 A m P y x) (@lem2747792 A m y P x)). Qed.
Lemma lem2747794 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) : (term199 A m P y) = (term200 A m y P).
Proof. exact (fun_ext (fun x : A => @lem2747793 A m y P x)). Qed.
Lemma lem2747795 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2747796 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) : (term201 A m P y) = (term202 A m y P).
Proof. exact (MK_COMB (@lem2747795 A) (@lem2747794 A m y P)). Qed.
Lemma lem2747797 {A : Type'} (m : A -> int) (P : A -> Prop) : (term203 A m P) = (term204 A m P).
Proof. exact (fun_ext (fun y : A -> A => @lem2747796 A m y P)). Qed.
Lemma lem2747798 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem2747799 {A : Type'} (m : A -> int) (P : A -> Prop) : (term186 A m P) = (term205 A m P).
Proof. exact (MK_COMB (@lem2747798 A) (@lem2747797 A m P)). Qed.
Lemma lem2747800 {A : Type'} (m : A -> int) (P : A -> Prop) : ((term185 A m P) = (term186 A m P)) = ((term180 A m P) = (term205 A m P)).
Proof. exact (MK_COMB (@lem2747788 A m P) (@lem2747799 A m P)). Qed.
Lemma lem2747801 {A : Type'} (m : A -> int) (P : A -> Prop) : (term180 A m P) = (term205 A m P).
Proof. exact (EQ_MP (@lem2747800 A m P) (@lem2747775 A m P)). Qed.
Lemma lem2747803 {A : Type'} (m : A -> int) (P : A -> Prop) : (term161 A m P) = (term205 A m P).
Proof. exact (TRANS (@lem2747771 A m P) (@lem2747801 A m P)). Qed.
Lemma lem2747804 {A : Type'} (m : A -> int) (P : A -> Prop) : (term22 A m P) = (term205 A m P).
Proof. exact (TRANS (@lem2747663 A m P) (@lem2747803 A m P)). Qed.
Lemma lem2747805 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term22 A m P) : term205 A m P.
Proof. exact (EQ_MP (@lem2747804 A m P) (@lem2747616 A m P h1)). Qed.
Lemma lem2747820 {A : Type'} (m : A -> int) (i' : int) (P : A -> Prop) (x : A) : (term126 A m i' P x) = (term206 A m i' P x).
Proof. exact (@lem17265 ((m x) = i') (P x)). Qed.
Lemma lem2747821 {A : Type'} (m : A -> int) (i' : int) (P : A -> Prop) : (term127 A m i' P) = (term207 A m i' P).
Proof. exact (fun_ext (fun x : A => @lem2747820 A m i' P x)). Qed.
Lemma lem2747822 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2747823 {A : Type'} (m : A -> int) (i' : int) (P : A -> Prop) : (term94 A m i' P) = (term208 A m i' P).
Proof. exact (MK_COMB (@lem2747822 A) (@lem2747821 A m i' P)). Qed.
Lemma lem2747825 (i' : int) (i : int) : (term209 i' i) = (term209 i' i).
Proof. exact (eq_refl (term209 i' i)). Qed.
Lemma lem2747826 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term210 A i m i' P) = (term211 A i m i' P).
Proof. exact (MK_COMB (@lem2747825 i' i) (@lem2747823 A m i' P)). Qed.
Lemma lem2747827 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term129 A i m i' P) = (term210 A i m i' P).
Proof. exact (@lem17265 (int_lt i' i) (term94 A m i' P)). Qed.
Lemma lem2747828 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term129 A i m i' P) = (term211 A i m i' P).
Proof. exact (TRANS (@lem2747827 A i m i' P) (@lem2747826 A i m i' P)). Qed.
Lemma lem2747830 (i' : int) : (term212 i') = (term212 i').
Proof. exact (eq_refl (term212 i')). Qed.
Lemma lem2747831 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term213 A i m i' P) = (term214 A i m i' P).
Proof. exact (MK_COMB (@lem2747830 i') (@lem2747828 A i m i' P)). Qed.
Lemma lem2747832 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term130 A i m i' P) = (term213 A i m i' P).
Proof. exact (@lem17265 (term215 i') (term129 A i m i' P)). Qed.
Lemma lem2747833 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term130 A i m i' P) = (term214 A i m i' P).
Proof. exact (TRANS (@lem2747832 A i m i' P) (@lem2747831 A i m i' P)). Qed.
Lemma lem2747834 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) : (term131 A i m P) = (term216 A i m P).
Proof. exact (fun_ext (fun i' : int => @lem2747833 A i m i' P)). Qed.
Lemma lem2747835 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2747920 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) : (term132 A i m P) = (term217 A i m P).
Proof. exact (MK_COMB (@lem2747835) (@lem2747834 A i m P)). Qed.
Lemma lem2747921 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) (h1 : term132 A i m P) : term217 A i m P.
Proof. exact (EQ_MP (@lem2747920 A i m P) (@lem2747618 A i m P h1)). Qed.
Lemma lem2747927 {A : Type'} (m : A -> int) (x : A) (i : int) (h1 : (m x) = i) : (m x) = i.
Proof. exact (h1). Qed.
Lemma lem2747933 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term143 A P x.
Proof. exact (h1). Qed.
Lemma lem2747934 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term202 A m y P.
Proof. exact (h1). Qed.
Lemma lem2747945 {A : Type'} (m : A -> int) (x : A) : (term140 A m x) = (term140 A m x).
Proof. exact (eq_refl (term140 A m x)). Qed.
Lemma lem2747946 {A : Type'} (m : A -> int) : (term141 A m) = (term141 A m).
Proof. exact (fun_ext (fun x : A => @lem2747945 A m x)). Qed.
Lemma lem2747947 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2747948 {A : Type'} (m : A -> int) : (term23 A m) = (term23 A m).
Proof. exact (MK_COMB (@lem2747947 A) (@lem2747946 A m)). Qed.
Lemma lem2747949 {A : Type'} (m : A -> int) (h1 : term23 A m) : term23 A m.
Proof. exact (EQ_MP (@lem2747948 A m) (@lem2747637 A m h1)). Qed.
Lemma lem2747974 {A : Type'} (m : A -> int) (i' : int) (P : A -> Prop) (x : A) : (term206 A m i' P x) = (term206 A m i' P x).
Proof. exact (eq_refl (term206 A m i' P x)). Qed.
Lemma lem2747975 {A : Type'} (m : A -> int) (i' : int) (P : A -> Prop) : (term207 A m i' P) = (term207 A m i' P).
Proof. exact (fun_ext (fun x : A => @lem2747974 A m i' P x)). Qed.
Lemma lem2747976 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2747977 {A : Type'} (m : A -> int) (i' : int) (P : A -> Prop) : (term208 A m i' P) = (term208 A m i' P).
Proof. exact (MK_COMB (@lem2747976 A) (@lem2747975 A m i' P)). Qed.
Lemma lem2747986 (i' : int) (i : int) : (term209 i' i) = (term209 i' i).
Proof. exact (eq_refl (term209 i' i)). Qed.
Lemma lem2747987 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term211 A i m i' P) = (term211 A i m i' P).
Proof. exact (MK_COMB (@lem2747986 i' i) (@lem2747977 A m i' P)). Qed.
Lemma lem2748000 (i' : int) : (term212 i') = (term212 i').
Proof. exact (eq_refl (term212 i')). Qed.
Lemma lem2748001 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term214 A i m i' P) = (term214 A i m i' P).
Proof. exact (MK_COMB (@lem2748000 i') (@lem2747987 A i m i' P)). Qed.
Lemma lem2748002 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) : (term216 A i m P) = (term216 A i m P).
Proof. exact (fun_ext (fun i' : int => @lem2748001 A i m i' P)). Qed.
Lemma lem2748003 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2748004 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) : (term217 A i m P) = (term217 A i m P).
Proof. exact (MK_COMB (@lem2748003) (@lem2748002 A i m P)). Qed.
Lemma lem2748005 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) (h1 : term132 A i m P) : term217 A i m P.
Proof. exact (EQ_MP (@lem2748004 A i m P) (@lem2747921 A i m P h1)). Qed.
Lemma lem2748013 {A : Type'} (m : A -> int) (x : A) (i : int) (h1 : (m x) = i) : (m x) = i.
Proof. exact (h1). Qed.
Lemma lem2748019 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term143 A P x.
Proof. exact (h1). Qed.
Lemma lem2748046 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (x : A) : (term198 A m y P x) = (term198 A m y P x).
Proof. exact (eq_refl (term198 A m y P x)). Qed.
Lemma lem2748047 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) : (term200 A m y P) = (term200 A m y P).
Proof. exact (fun_ext (fun x : A => @lem2748046 A m y P x)). Qed.
Lemma lem2748048 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748049 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) : (term202 A m y P) = (term202 A m y P).
Proof. exact (MK_COMB (@lem2748048 A) (@lem2748047 A m y P)). Qed.
Lemma lem2748050 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term202 A m y P.
Proof. exact (EQ_MP (@lem2748049 A m y P) (@lem2747934 A m y P h1)). Qed.
Lemma lem2748052 {A : Type'} (m : A -> int) (x : A) : (term140 A m x) = (term140 A m x).
Proof. exact (eq_refl (term140 A m x)). Qed.
Lemma lem2748053 {A : Type'} (m : A -> int) : (term141 A m) = (term141 A m).
Proof. exact (fun_ext (fun x : A => @lem2748052 A m x)). Qed.
Lemma lem2748054 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748056 {A : Type'} (m : A -> int) : (term23 A m) = (term23 A m).
Proof. exact (MK_COMB (@lem2748054 A) (@lem2748053 A m)). Qed.
Lemma lem2748057 {A : Type'} (m : A -> int) (h1 : term23 A m) : term23 A m.
Proof. exact (EQ_MP (@lem2748056 A m) (@lem2747949 A m h1)). Qed.
Lemma lem2748063 {A : Type'} (P : Prop) (Q : A -> Prop) : (term218 A P Q) = (term219 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem2748064 {A : Type'} (P : Prop) (Q : A -> Prop) : (term218 A P Q) = (term219 A P Q).
Proof. exact (@lem2748063 A P Q). Qed.
Lemma lem2748065 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term220 A i m i' P) = (term221 A i m i' P).
Proof. exact (@lem2748064 A (term222 i' i) (term207 A m i' P)). Qed.
Lemma lem2748066 {A : Type'} (m : A -> int) (i' : int) (P : A -> Prop) (x : A) : (term223 A m i' P x) = (term206 A m i' P x).
Proof. exact (eq_refl (term223 A m i' P x)). Qed.
Lemma lem2748067 {A : Type'} (m : A -> int) (i' : int) (P : A -> Prop) : (term224 A m i' P) = (term207 A m i' P).
Proof. exact (fun_ext (fun x : A => @lem2748066 A m i' P x)). Qed.
Lemma lem2748068 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748069 {A : Type'} (m : A -> int) (i' : int) (P : A -> Prop) : (term225 A m i' P) = (term208 A m i' P).
Proof. exact (MK_COMB (@lem2748068 A) (@lem2748067 A m i' P)). Qed.
Lemma lem2748070 (i' : int) (i : int) : (term209 i' i) = (term209 i' i).
Proof. exact (eq_refl (term209 i' i)). Qed.
Lemma lem2748071 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term220 A i m i' P) = (term211 A i m i' P).
Proof. exact (MK_COMB (@lem2748070 i' i) (@lem2748069 A m i' P)). Qed.
Lemma lem2748072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2748073 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term226 A i m i' P) = (term227 A i m i' P).
Proof. exact (MK_COMB (@lem2748072) (@lem2748071 A i m i' P)). Qed.
Lemma lem2748074 {A : Type'} (m : A -> int) (i' : int) (P : A -> Prop) (x : A) : (term223 A m i' P x) = (term206 A m i' P x).
Proof. exact (eq_refl (term223 A m i' P x)). Qed.
Lemma lem2748075 (i' : int) (i : int) : (term209 i' i) = (term209 i' i).
Proof. exact (eq_refl (term209 i' i)). Qed.
Lemma lem2748076 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) (x : A) : (term228 A i m i' P x) = (term229 A i m i' P x).
Proof. exact (MK_COMB (@lem2748075 i' i) (@lem2748074 A m i' P x)). Qed.
Lemma lem2748077 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term230 A i m i' P) = (term231 A i m i' P).
Proof. exact (fun_ext (fun x : A => @lem2748076 A i m i' P x)). Qed.
Lemma lem2748078 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748079 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term221 A i m i' P) = (term232 A i m i' P).
Proof. exact (MK_COMB (@lem2748078 A) (@lem2748077 A i m i' P)). Qed.
Lemma lem2748080 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : ((term220 A i m i' P) = (term221 A i m i' P)) = ((term211 A i m i' P) = (term232 A i m i' P)).
Proof. exact (MK_COMB (@lem2748073 A i m i' P) (@lem2748079 A i m i' P)). Qed.
Lemma lem2748081 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term211 A i m i' P) = (term232 A i m i' P).
Proof. exact (EQ_MP (@lem2748080 A i m i' P) (@lem2748065 A i m i' P)). Qed.
Lemma lem2748082 (i' : int) : (term212 i') = (term212 i').
Proof. exact (eq_refl (term212 i')). Qed.
Lemma lem2748083 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term214 A i m i' P) = (term233 A i m i' P).
Proof. exact (MK_COMB (@lem2748082 i') (@lem2748081 A i m i' P)). Qed.
Lemma lem2748085 {A : Type'} (P : Prop) (Q : A -> Prop) : (term218 A P Q) = (term219 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem2748086 {A : Type'} (P : Prop) (Q : A -> Prop) : (term218 A P Q) = (term219 A P Q).
Proof. exact (@lem2748085 A P Q). Qed.
Lemma lem2748087 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term234 A i m i' P) = (term235 A i m i' P).
Proof. exact (@lem2748086 A (term236 i') (term231 A i m i' P)). Qed.
Lemma lem2748088 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) (x : A) : (term237 A i m i' P x) = (term229 A i m i' P x).
Proof. exact (eq_refl (term237 A i m i' P x)). Qed.
Lemma lem2748089 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term238 A i m i' P) = (term231 A i m i' P).
Proof. exact (fun_ext (fun x : A => @lem2748088 A i m i' P x)). Qed.
Lemma lem2748090 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748091 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term239 A i m i' P) = (term232 A i m i' P).
Proof. exact (MK_COMB (@lem2748090 A) (@lem2748089 A i m i' P)). Qed.
Lemma lem2748092 (i' : int) : (term212 i') = (term212 i').
Proof. exact (eq_refl (term212 i')). Qed.
Lemma lem2748093 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term234 A i m i' P) = (term233 A i m i' P).
Proof. exact (MK_COMB (@lem2748092 i') (@lem2748091 A i m i' P)). Qed.
Lemma lem2748094 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2748095 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term240 A i m i' P) = (term241 A i m i' P).
Proof. exact (MK_COMB (@lem2748094) (@lem2748093 A i m i' P)). Qed.
Lemma lem2748096 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) (x : A) : (term237 A i m i' P x) = (term229 A i m i' P x).
Proof. exact (eq_refl (term237 A i m i' P x)). Qed.
Lemma lem2748097 (i' : int) : (term212 i') = (term212 i').
Proof. exact (eq_refl (term212 i')). Qed.
Lemma lem2748098 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) (x : A) : (term242 A i m i' P x) = (term243 A i m i' P x).
Proof. exact (MK_COMB (@lem2748097 i') (@lem2748096 A i m i' P x)). Qed.
Lemma lem2748099 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term244 A i m i' P) = (term245 A i m i' P).
Proof. exact (fun_ext (fun x : A => @lem2748098 A i m i' P x)). Qed.
Lemma lem2748100 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748101 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term235 A i m i' P) = (term246 A i m i' P).
Proof. exact (MK_COMB (@lem2748100 A) (@lem2748099 A i m i' P)). Qed.
Lemma lem2748102 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : ((term234 A i m i' P) = (term235 A i m i' P)) = ((term233 A i m i' P) = (term246 A i m i' P)).
Proof. exact (MK_COMB (@lem2748095 A i m i' P) (@lem2748101 A i m i' P)). Qed.
Lemma lem2748103 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term233 A i m i' P) = (term246 A i m i' P).
Proof. exact (EQ_MP (@lem2748102 A i m i' P) (@lem2748087 A i m i' P)). Qed.
Lemma lem2748104 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term214 A i m i' P) = (term246 A i m i' P).
Proof. exact (TRANS (@lem2748083 A i m i' P) (@lem2748103 A i m i' P)). Qed.
Lemma lem2748105 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) : (term216 A i m P) = (term247 A i m P).
Proof. exact (fun_ext (fun i' : int => @lem2748104 A i m i' P)). Qed.
Lemma lem2748106 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2748107 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) : (term217 A i m P) = (term248 A i m P).
Proof. exact (MK_COMB (@lem2748106) (@lem2748105 A i m P)). Qed.
Lemma lem2748126 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) (x : A) : (term243 A i m i' P x) = (term243 A i m i' P x).
Proof. exact (eq_refl (term243 A i m i' P x)). Qed.
Lemma lem2748127 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term245 A i m i' P) = (term245 A i m i' P).
Proof. exact (fun_ext (fun x : A => @lem2748126 A i m i' P x)). Qed.
Lemma lem2748128 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748129 {A : Type'} (i : int) (m : A -> int) (i' : int) (P : A -> Prop) : (term246 A i m i' P) = (term246 A i m i' P).
Proof. exact (MK_COMB (@lem2748128 A) (@lem2748127 A i m i' P)). Qed.
Lemma lem2748130 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) : (term247 A i m P) = (term247 A i m P).
Proof. exact (fun_ext (fun i' : int => @lem2748129 A i m i' P)). Qed.
Lemma lem2748131 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2748132 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) : (term248 A i m P) = (term248 A i m P).
Proof. exact (MK_COMB (@lem2748131) (@lem2748130 A i m P)). Qed.
Lemma lem2748133 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) : (term217 A i m P) = (term248 A i m P).
Proof. exact (TRANS (@lem2748107 A i m P) (@lem2748132 A i m P)). Qed.
Lemma lem2748134 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) (h1 : term132 A i m P) : term248 A i m P.
Proof. exact (EQ_MP (@lem2748133 A i m P) (@lem2748005 A i m P h1)). Qed.
Lemma lem2748138 {A : Type'} (m : A -> int) (x : A) (i : int) (h1 : (m x) = i) : (m x) = i.
Proof. exact (h1). Qed.
Lemma lem2748142 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term143 A P x.
Proof. exact (h1). Qed.
Lemma lem2748160 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (x : A) : (term198 A m y P x) = (term249 A m y P x).
Proof. exact (@lem19699 (term250 A y m x) (term251 A P y x) (P x)). Qed.
Lemma lem2748161 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) : (term200 A m y P) = (term252 A m y P).
Proof. exact (fun_ext (fun x : A => @lem2748160 A m y P x)). Qed.
Lemma lem2748162 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748164 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) : (term202 A m y P) = (term253 A m y P).
Proof. exact (MK_COMB (@lem2748162 A) (@lem2748161 A m y P)). Qed.
Lemma lem2748165 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term253 A m y P.
Proof. exact (EQ_MP (@lem2748164 A m y P) (@lem2748050 A m y P h1)). Qed.
Lemma lem2748166 {A : Type'} (_30547 : A) (m : A -> int) (h1 : term23 A m) : term254 A m _30547.
Proof. exact (@lem2748057 A m h1 _30547). Qed.
Lemma lem2748167 {A : Type'} (m : A -> int) (_30547 : A) : (term254 A m _30547) = (term140 A m _30547).
Proof. exact (eq_refl (term254 A m _30547)). Qed.
Lemma lem2748169 {A : Type'} (_30548 : int) (i : int) (m : A -> int) (P : A -> Prop) (h1 : term132 A i m P) : term255 A i m P _30548.
Proof. exact (@lem2748134 A i m P h1 _30548). Qed.
Lemma lem2748170 {A : Type'} (i : int) (m : A -> int) (_30548 : int) (P : A -> Prop) : (term255 A i m P _30548) = (term246 A i m _30548 P).
Proof. exact (eq_refl (term255 A i m P _30548)). Qed.
Lemma lem2748171 {A : Type'} (_30548 : int) (i : int) (m : A -> int) (P : A -> Prop) (h1 : term132 A i m P) : term246 A i m _30548 P.
Proof. exact (EQ_MP (@lem2748170 A i m _30548 P) (@lem2748169 A _30548 i m P h1)). Qed.
Lemma lem2748172 {A : Type'} (_30548 : int) (_30549 : A) (i : int) (m : A -> int) (P : A -> Prop) (h1 : term132 A i m P) : term256 A i m _30548 P _30549.
Proof. exact (@lem2748171 A _30548 i m P h1 _30549). Qed.
Lemma lem2748173 {A : Type'} (i : int) (m : A -> int) (_30548 : int) (P : A -> Prop) (_30549 : A) : (term256 A i m _30548 P _30549) = (term243 A i m _30548 P _30549).
Proof. exact (eq_refl (term256 A i m _30548 P _30549)). Qed.
Lemma lem2748175 {A : Type'} (_30550 : A) (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term257 A m y P _30550.
Proof. exact (@lem2748165 A m y P h1 _30550). Qed.
Lemma lem2748176 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (_30550 : A) : (term257 A m y P _30550) = (term249 A m y P _30550).
Proof. exact (eq_refl (term257 A m y P _30550)). Qed.
Lemma lem2748177 {A : Type'} (_30550 : A) (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term249 A m y P _30550.
Proof. exact (EQ_MP (@lem2748176 A m y P _30550) (@lem2748175 A _30550 m y P h1)). Qed.
Lemma lem2748197 {A : Type'} (_30548 : int) (_30549 : A) (i : int) (m : A -> int) (P : A -> Prop) (h1 : term132 A i m P) : term243 A i m _30548 P _30549.
Proof. exact (EQ_MP (@lem2748173 A i m _30548 P _30549) (@lem2748172 A _30548 _30549 i m P h1)). Qed.
Lemma lem2748199 {A : Type'} (m : A -> int) (x : A) (i : int) (h1 : (m x) = i) : (m x) = i.
Proof. exact (h1). Qed.
Lemma lem2748201 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term143 A P x.
Proof. exact (h1). Qed.
Lemma lem2748214 {A : Type'} (m : A -> int) (x : A) (i : int) (h1 : (m x) = i) : i = (m x).
Proof. exact (SYM (@lem2748199 A m x i h1)). Qed.
Lemma lem2748256 {A : Type'} (m : A -> int) (_30548 : int) (P : A -> Prop) (_30549 : A) : (term258 A m _30548 P _30549) = (term258 A m _30548 P _30549).
Proof. exact (eq_refl (term258 A m _30548 P _30549)). Qed.
Lemma lem2748257 {A : Type'} (_30548 : int) (P : A -> Prop) (_30549 : A) (m : A -> int) (x : A) (i : int) (h1 : (m x) = i) : (term259 A m _30548 P _30549 i) = (term260 A _30548 P _30549 m x).
Proof. exact (MK_COMB (@lem2748256 A m _30548 P _30549) (@lem2748214 A m x i h1)). Qed.
Lemma lem2748258 {A : Type'} (x : A) (m : A -> int) (_30548 : int) (P : A -> Prop) (_30549 : A) : (term260 A _30548 P _30549 m x) = (term261 A x m _30548 P _30549).
Proof. exact (eq_refl (term260 A _30548 P _30549 m x)). Qed.
Lemma lem2748259 {A : Type'} (m : A -> int) (_30548 : int) (P : A -> Prop) (_30549 : A) (i : int) : (term262 A m _30548 P _30549 i) = (term262 A m _30548 P _30549 i).
Proof. exact (eq_refl (term262 A m _30548 P _30549 i)). Qed.
Lemma lem2748260 {A : Type'} (i : int) (x : A) (m : A -> int) (_30548 : int) (P : A -> Prop) (_30549 : A) : ((term259 A m _30548 P _30549 i) = (term260 A _30548 P _30549 m x)) = ((term259 A m _30548 P _30549 i) = (term261 A x m _30548 P _30549)).
Proof. exact (MK_COMB (@lem2748259 A m _30548 P _30549 i) (@lem2748258 A x m _30548 P _30549)). Qed.
Lemma lem2748261 {A : Type'} (i : int) (m : A -> int) (_30548 : int) (P : A -> Prop) (_30549 : A) : (term259 A m _30548 P _30549 i) = (term243 A i m _30548 P _30549).
Proof. exact (eq_refl (term259 A m _30548 P _30549 i)). Qed.
Lemma lem2748262 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2748263 {A : Type'} (i : int) (m : A -> int) (_30548 : int) (P : A -> Prop) (_30549 : A) : (term262 A m _30548 P _30549 i) = (term263 A i m _30548 P _30549).
Proof. exact (MK_COMB (@lem2748262) (@lem2748261 A i m _30548 P _30549)). Qed.
Lemma lem2748264 {A : Type'} (x : A) (m : A -> int) (_30548 : int) (P : A -> Prop) (_30549 : A) : (term261 A x m _30548 P _30549) = (term261 A x m _30548 P _30549).
Proof. exact (eq_refl (term261 A x m _30548 P _30549)). Qed.
Lemma lem2748265 {A : Type'} (i : int) (x : A) (m : A -> int) (_30548 : int) (P : A -> Prop) (_30549 : A) : ((term259 A m _30548 P _30549 i) = (term261 A x m _30548 P _30549)) = ((term243 A i m _30548 P _30549) = (term261 A x m _30548 P _30549)).
Proof. exact (MK_COMB (@lem2748263 A i m _30548 P _30549) (@lem2748264 A x m _30548 P _30549)). Qed.
Lemma lem2748266 {A : Type'} (i : int) (x : A) (m : A -> int) (_30548 : int) (P : A -> Prop) (_30549 : A) : ((term259 A m _30548 P _30549 i) = (term260 A _30548 P _30549 m x)) = ((term243 A i m _30548 P _30549) = (term261 A x m _30548 P _30549)).
Proof. exact (TRANS (@lem2748260 A i x m _30548 P _30549) (@lem2748265 A i x m _30548 P _30549)). Qed.
Lemma lem2748267 {A : Type'} (_30548 : int) (P : A -> Prop) (_30549 : A) (m : A -> int) (x : A) (i : int) (h1 : (m x) = i) : (term243 A i m _30548 P _30549) = (term261 A x m _30548 P _30549).
Proof. exact (EQ_MP (@lem2748266 A i x m _30548 P _30549) (@lem2748257 A _30548 P _30549 m x i h1)). Qed.
Lemma lem2748268 {A : Type'} (_30548 : int) (_30549 : A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term132 A i m P) (h2 : (m x) = i) : term261 A x m _30548 P _30549.
Proof. exact (EQ_MP (@lem2748267 A _30548 P _30549 m x i h2) (@lem2748197 A _30548 _30549 i m P h1)). Qed.
Lemma lem2748282 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term143 A P x.
Proof. exact (h1). Qed.
Lemma lem2748296 {A : Type'} (_30550 : A) (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term264 A y m P _30550.
Proof. exact (proj1 (@lem2748177 A _30550 m y P h1)). Qed.
Lemma lem2748310 {A : Type'} (_30550 : A) (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term265 A y P _30550.
Proof. exact (proj2 (@lem2748177 A _30550 m y P h1)). Qed.
Lemma lem2748400 {A : Type'} (_30547 : A) (m : A -> int) (h1 : term23 A m) : term140 A m _30547.
Proof. exact (EQ_MP (@lem2748167 A m _30547) (@lem2748166 A _30547 m h1)). Qed.
Lemma lem2748401 {A : Type'} (_30547 : A) (m : A -> int) (h1 : term23 A m) : term140 A m _30547.
Proof. exact (@lem2748400 A _30547 m h1). Qed.
Lemma lem2748402 {A : Type'} (y : A -> A) (x : A) (m : A -> int) (h1 : term23 A m) : term266 A m y x.
Proof. exact (@lem2748401 A (y x) m h1). Qed.
Lemma lem2748403 {A : Type'} (y : A -> A) (x : A) (m : A -> int) (h1 : term23 A m) : term267 A m y x.
Proof. exact (fun h0 : term268 A m y x => @lem2748402 A y x m h1). Qed.
Lemma lem2748405 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2748406 {A : Type'} (m : A -> int) (y : A -> A) (x : A) : (term267 A m y x) = (term266 A m y x).
Proof. exact (@lem2748405 (term266 A m y x)). Qed.
Lemma lem2748407 {A : Type'} (y : A -> A) (x : A) (m : A -> int) (h1 : term23 A m) : term266 A m y x.
Proof. exact (EQ_MP (@lem2748406 A m y x) (@lem2748403 A y x m h1)). Qed.
Lemma lem2748410 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term143 A P x.
Proof. exact (h1). Qed.
Lemma lem2748411 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term270 A P x.
Proof. exact (fun h0 : P x => @lem2748410 A P x h1). Qed.
Lemma lem2748413 (p : Prop) : (term271 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2748414 {A : Type'} (P : A -> Prop) (x : A) : (term270 A P x) = (term143 A P x).
Proof. exact (@lem2748413 (P x)). Qed.
Lemma lem2748415 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term143 A P x.
Proof. exact (EQ_MP (@lem2748414 A P x) (@lem2748411 A P x h1)). Qed.
Lemma lem2748417 (b : Prop) (a : Prop) : (a \/ b) = (term272 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2748420 {A : Type'} (P : A -> Prop) (y : A -> A) (m : A -> int) (_30550 : A) : (term264 A y m P _30550) = (term273 A P y m _30550).
Proof. exact (@lem2748417 (P _30550) (term250 A y m _30550)). Qed.
Lemma lem2748423 {A : Type'} (_30550 : A) (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term273 A P y m _30550.
Proof. exact (EQ_MP (@lem2748420 A P y m _30550) (@lem2748296 A _30550 m y P h1)). Qed.
Lemma lem2748424 {A : Type'} (_30550 : A) (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term273 A P y m _30550.
Proof. exact (@lem2748423 A _30550 m y P h1). Qed.
Lemma lem2748425 {A : Type'} (x : A) (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term273 A P y m x.
Proof. exact (@lem2748424 A x m y P h1). Qed.
Lemma lem2748428 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (x : A) (h1 : term202 A m y P) (h2 : term143 A P x) : term250 A y m x.
Proof. exact (@lem2748425 A x m y P h1 (@lem2748415 A P x h2)). Qed.
Lemma lem2748429 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (x : A) (h1 : term202 A m y P) (h2 : term143 A P x) : term274 A y m x.
Proof. exact (fun h0 : term275 A y m x => @lem2748428 A m y P x h1 h2). Qed.
Lemma lem2748431 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2748432 {A : Type'} (y : A -> A) (m : A -> int) (x : A) : (term274 A y m x) = (term250 A y m x).
Proof. exact (@lem2748431 (term250 A y m x)). Qed.
Lemma lem2748433 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (x : A) (h1 : term202 A m y P) (h2 : term143 A P x) : term250 A y m x.
Proof. exact (EQ_MP (@lem2748432 A y m x) (@lem2748429 A m y P x h1 h2)). Qed.
Lemma lem2748435 (x : int) : x = x.
Proof. exact (@lem21386 int x). Qed.
Lemma lem2748436 {A : Type'} (m : A -> int) (y : A -> A) (x : A) : (term276 A m y x) = (term276 A m y x).
Proof. exact (@lem2748435 (term276 A m y x)). Qed.
Lemma lem2748437 {A : Type'} (m : A -> int) (y : A -> A) (x : A) : term277 A m y x.
Proof. exact (fun h0 : term278 A m y x => @lem2748436 A m y x). Qed.
Lemma lem2748439 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2748440 {A : Type'} (m : A -> int) (y : A -> A) (x : A) : (term277 A m y x) = ((term276 A m y x) = (term276 A m y x)).
Proof. exact (@lem2748439 ((term276 A m y x) = (term276 A m y x))). Qed.
Lemma lem2748441 {A : Type'} (m : A -> int) (y : A -> A) (x : A) : (term276 A m y x) = (term276 A m y x).
Proof. exact (EQ_MP (@lem2748440 A m y x) (@lem2748437 A m y x)). Qed.
Lemma lem2748457 (q : Prop) (p : Prop) (r : Prop) : (term279 p q r) = (term279 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2748458 {A : Type'} (_30548 : int) (m : A -> int) (x : A) (P : A -> Prop) (_30549 : A) : (term280 A x m _30548 P _30549) = (term281 A _30548 m x P _30549).
Proof. exact (@lem2748457 (term282 A m _30549 _30548) (term283 A _30548 m x) (P _30549)). Qed.
Lemma lem2748474 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2748475 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term284 A _30548 m x P _30549) = (term285 A P _30549 _30548 m x).
Proof. exact (@lem2748474 (P _30549) (term283 A _30548 m x)). Qed.
Lemma lem2748481 {A : Type'} (m : A -> int) (_30549 : A) (_30548 : int) : (term286 A m _30549 _30548) = (term286 A m _30549 _30548).
Proof. exact (eq_refl (term286 A m _30549 _30548)). Qed.
Lemma lem2748482 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term281 A _30548 m x P _30549) = (term287 A P _30549 _30548 m x).
Proof. exact (MK_COMB (@lem2748481 A m _30549 _30548) (@lem2748475 A P _30549 _30548 m x)). Qed.
Lemma lem2748486 (q : Prop) (p : Prop) (r : Prop) : (term279 p q r) = (term279 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2748487 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term287 A P _30549 _30548 m x) = (term288 A P _30549 _30548 m x).
Proof. exact (@lem2748486 (P _30549) (term282 A m _30549 _30548) (term283 A _30548 m x)). Qed.
Lemma lem2748505 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term281 A _30548 m x P _30549) = (term288 A P _30549 _30548 m x).
Proof. exact (TRANS (@lem2748482 A P _30549 _30548 m x) (@lem2748487 A P _30549 _30548 m x)). Qed.
Lemma lem2748506 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term280 A x m _30548 P _30549) = (term288 A P _30549 _30548 m x).
Proof. exact (TRANS (@lem2748458 A _30548 m x P _30549) (@lem2748505 A P _30549 _30548 m x)). Qed.
Lemma lem2748507 (_30548 : int) : (term212 _30548) = (term212 _30548).
Proof. exact (eq_refl (term212 _30548)). Qed.
Lemma lem2748508 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term261 A x m _30548 P _30549) = (term289 A P _30549 _30548 m x).
Proof. exact (MK_COMB (@lem2748507 _30548) (@lem2748506 A P _30549 _30548 m x)). Qed.
Lemma lem2748512 (q : Prop) (p : Prop) (r : Prop) : (term279 p q r) = (term279 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2748513 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term289 A P _30549 _30548 m x) = (term290 A P _30549 _30548 m x).
Proof. exact (@lem2748512 (P _30549) (term236 _30548) (term291 A _30549 _30548 m x)). Qed.
Lemma lem2748527 (q : Prop) (p : Prop) (r : Prop) : (term279 p q r) = (term279 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2748528 {A : Type'} (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term292 A _30549 _30548 m x) = (term293 A _30549 _30548 m x).
Proof. exact (@lem2748527 (term282 A m _30549 _30548) (term236 _30548) (term283 A _30548 m x)). Qed.
Lemma lem2748546 {A : Type'} (P : A -> Prop) (_30549 : A) : (term294 A P _30549) = (term294 A P _30549).
Proof. exact (eq_refl (term294 A P _30549)). Qed.
Lemma lem2748547 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term290 A P _30549 _30548 m x) = (term295 A P _30549 _30548 m x).
Proof. exact (MK_COMB (@lem2748546 A P _30549) (@lem2748528 A _30549 _30548 m x)). Qed.
Lemma lem2748558 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term289 A P _30549 _30548 m x) = (term295 A P _30549 _30548 m x).
Proof. exact (TRANS (@lem2748513 A P _30549 _30548 m x) (@lem2748547 A P _30549 _30548 m x)). Qed.
Lemma lem2748559 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term261 A x m _30548 P _30549) = (term295 A P _30549 _30548 m x).
Proof. exact (TRANS (@lem2748508 A P _30549 _30548 m x) (@lem2748558 A P _30549 _30548 m x)). Qed.
Lemma lem2748560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2748561 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term296 A x m _30548 P _30549) = (term297 A P _30549 _30548 m x).
Proof. exact (MK_COMB (@lem2748560) (@lem2748559 A P _30549 _30548 m x)). Qed.
Lemma lem2748585 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2748586 {A : Type'} (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term298 A x m _30549 _30548) = (term291 A _30549 _30548 m x).
Proof. exact (@lem2748585 (term282 A m _30549 _30548) (term283 A _30548 m x)). Qed.
Lemma lem2748594 (_30548 : int) : (term212 _30548) = (term212 _30548).
Proof. exact (eq_refl (term212 _30548)). Qed.
Lemma lem2748595 {A : Type'} (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term299 A x m _30549 _30548) = (term292 A _30549 _30548 m x).
Proof. exact (MK_COMB (@lem2748594 _30548) (@lem2748586 A _30549 _30548 m x)). Qed.
Lemma lem2748599 (q : Prop) (p : Prop) (r : Prop) : (term279 p q r) = (term279 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2748600 {A : Type'} (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term292 A _30549 _30548 m x) = (term293 A _30549 _30548 m x).
Proof. exact (@lem2748599 (term282 A m _30549 _30548) (term236 _30548) (term283 A _30548 m x)). Qed.
Lemma lem2748618 {A : Type'} (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term299 A x m _30549 _30548) = (term293 A _30549 _30548 m x).
Proof. exact (TRANS (@lem2748595 A _30549 _30548 m x) (@lem2748600 A _30549 _30548 m x)). Qed.
Lemma lem2748619 {A : Type'} (P : A -> Prop) (_30549 : A) : (term294 A P _30549) = (term294 A P _30549).
Proof. exact (eq_refl (term294 A P _30549)). Qed.
Lemma lem2748620 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : (term300 A P x m _30549 _30548) = (term295 A P _30549 _30548 m x).
Proof. exact (MK_COMB (@lem2748619 A P _30549) (@lem2748618 A _30549 _30548 m x)). Qed.
Lemma lem2748631 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : ((term261 A x m _30548 P _30549) = (term300 A P x m _30549 _30548)) = ((term295 A P _30549 _30548 m x) = (term295 A P _30549 _30548 m x)).
Proof. exact (MK_COMB (@lem2748561 A P _30549 _30548 m x) (@lem2748620 A P _30549 _30548 m x)). Qed.
Lemma lem2748633 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2748634 (x : Prop) : (x = x) = True.
Proof. exact (@lem2748633 Prop x). Qed.
Lemma lem2748635 {A : Type'} (P : A -> Prop) (_30549 : A) (_30548 : int) (m : A -> int) (x : A) : ((term295 A P _30549 _30548 m x) = (term295 A P _30549 _30548 m x)) = True.
Proof. exact (@lem2748634 (term295 A P _30549 _30548 m x)). Qed.
Lemma lem2748636 {A : Type'} (P : A -> Prop) (x : A) (m : A -> int) (_30549 : A) (_30548 : int) : ((term261 A x m _30548 P _30549) = (term300 A P x m _30549 _30548)) = True.
Proof. exact (TRANS (@lem2748631 A P _30549 _30548 m x) (@lem2748635 A P _30549 _30548 m x)). Qed.
Lemma lem2748637 {A : Type'} (P : A -> Prop) (x : A) (m : A -> int) (_30549 : A) (_30548 : int) : True = ((term261 A x m _30548 P _30549) = (term300 A P x m _30549 _30548)).
Proof. exact (SYM (@lem2748636 A P x m _30549 _30548)). Qed.
Lemma lem2748638 {A : Type'} (P : A -> Prop) (x : A) (m : A -> int) (_30549 : A) (_30548 : int) : (term261 A x m _30548 P _30549) = (term300 A P x m _30549 _30548).
Proof. exact (EQ_MP (@lem2748637 A P x m _30549 _30548) (@lem0)). Qed.
Lemma lem2748639 {A : Type'} (_30549 : A) (_30548 : int) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term132 A i m P) (h2 : (m x) = i) : term300 A P x m _30549 _30548.
Proof. exact (EQ_MP (@lem2748638 A P x m _30549 _30548) (@lem2748268 A _30548 _30549 P m x i h1 h2)). Qed.
Lemma lem2748641 (b : Prop) (a : Prop) : (a \/ b) = (term272 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2748642 {A : Type'} (x : A) (m : A -> int) (_30548 : int) (P : A -> Prop) (_30549 : A) : (term300 A P x m _30549 _30548) = (term301 A x m _30548 P _30549).
Proof. exact (@lem2748641 (term299 A x m _30549 _30548) (P _30549)). Qed.
Lemma lem2748644 (a : Prop) (b : Prop) : (term302 a b) = (term303 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2748645 {A : Type'} (x : A) (m : A -> int) (_30549 : A) (_30548 : int) : (term304 A x m _30549 _30548) = (term305 A x m _30549 _30548).
Proof. exact (@lem2748644 (term236 _30548) (term298 A x m _30549 _30548)). Qed.
Lemma lem2748647 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2748648 (_30548 : int) : (term306 _30548) = (term215 _30548).
Proof. exact (@lem2748647 (term215 _30548)). Qed.
Lemma lem2748649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2748650 (_30548 : int) : (term307 _30548) = (term308 _30548).
Proof. exact (MK_COMB (@lem2748649) (@lem2748648 _30548)). Qed.
Lemma lem2748652 (a : Prop) (b : Prop) : (term302 a b) = (term303 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2748653 {A : Type'} (x : A) (m : A -> int) (_30549 : A) (_30548 : int) : (term309 A x m _30549 _30548) = (term310 A x m _30549 _30548).
Proof. exact (@lem2748652 (term283 A _30548 m x) (term282 A m _30549 _30548)). Qed.
Lemma lem2748655 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2748656 {A : Type'} (_30548 : int) (m : A -> int) (x : A) : (term311 A _30548 m x) = (term312 A _30548 m x).
Proof. exact (@lem2748655 (term312 A _30548 m x)). Qed.
Lemma lem2748657 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2748658 {A : Type'} (_30548 : int) (m : A -> int) (x : A) : (term313 A _30548 m x) = (term314 A _30548 m x).
Proof. exact (MK_COMB (@lem2748657) (@lem2748656 A _30548 m x)). Qed.
Lemma lem2748660 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2748661 {A : Type'} (m : A -> int) (_30549 : A) (_30548 : int) : (term315 A m _30549 _30548) = ((m _30549) = _30548).
Proof. exact (@lem2748660 ((m _30549) = _30548)). Qed.
Lemma lem2748662 {A : Type'} (x : A) (m : A -> int) (_30549 : A) (_30548 : int) : (term310 A x m _30549 _30548) = (term316 A x m _30549 _30548).
Proof. exact (MK_COMB (@lem2748658 A _30548 m x) (@lem2748661 A m _30549 _30548)). Qed.
Lemma lem2748663 {A : Type'} (x : A) (m : A -> int) (_30549 : A) (_30548 : int) : (term309 A x m _30549 _30548) = (term316 A x m _30549 _30548).
Proof. exact (TRANS (@lem2748653 A x m _30549 _30548) (@lem2748662 A x m _30549 _30548)). Qed.
Lemma lem2748664 {A : Type'} (x : A) (m : A -> int) (_30549 : A) (_30548 : int) : (term305 A x m _30549 _30548) = (term317 A x m _30549 _30548).
Proof. exact (MK_COMB (@lem2748650 _30548) (@lem2748663 A x m _30549 _30548)). Qed.
Lemma lem2748665 {A : Type'} (x : A) (m : A -> int) (_30549 : A) (_30548 : int) : (term304 A x m _30549 _30548) = (term317 A x m _30549 _30548).
Proof. exact (TRANS (@lem2748645 A x m _30549 _30548) (@lem2748664 A x m _30549 _30548)). Qed.
Lemma lem2748666 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2748667 {A : Type'} (x : A) (m : A -> int) (_30549 : A) (_30548 : int) : (term318 A x m _30549 _30548) = (term319 A x m _30549 _30548).
Proof. exact (MK_COMB (@lem2748666) (@lem2748665 A x m _30549 _30548)). Qed.
Lemma lem2748668 {A : Type'} (P : A -> Prop) (_30549 : A) : (P _30549) = (P _30549).
Proof. exact (eq_refl (P _30549)). Qed.
Lemma lem2748669 {A : Type'} (x : A) (m : A -> int) (_30548 : int) (P : A -> Prop) (_30549 : A) : (term301 A x m _30548 P _30549) = (term320 A x m _30548 P _30549).
Proof. exact (MK_COMB (@lem2748667 A x m _30549 _30548) (@lem2748668 A P _30549)). Qed.
Lemma lem2748670 {A : Type'} (x : A) (m : A -> int) (_30548 : int) (P : A -> Prop) (_30549 : A) : (term300 A P x m _30549 _30548) = (term320 A x m _30548 P _30549).
Proof. exact (TRANS (@lem2748642 A x m _30548 P _30549) (@lem2748669 A x m _30548 P _30549)). Qed.
Lemma lem2748672 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (x : A) (h1 : term202 A m y P) (h2 : term143 A P x) : term321 A m y x.
Proof. exact (conj (@lem2748433 A m y P x h1 h2) (@lem2748441 A m y x)). Qed.
Lemma lem2748673 {A : Type'} (y : A -> A) (m : A -> int) (P : A -> Prop) (x : A) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term143 A P x) : term322 A m y x.
Proof. exact (conj (@lem2748407 A y x m h2) (@lem2748672 A m y P x h1 h3)). Qed.
Lemma lem2748675 {A : Type'} (_30548 : int) (_30549 : A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term132 A i m P) (h2 : (m x) = i) : term320 A x m _30548 P _30549.
Proof. exact (EQ_MP (@lem2748670 A x m _30548 P _30549) (@lem2748639 A _30549 _30548 P m x i h1 h2)). Qed.
Lemma lem2748676 {A : Type'} (_30548 : int) (_30549 : A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term132 A i m P) (h2 : (m x) = i) : term320 A x m _30548 P _30549.
Proof. exact (@lem2748675 A _30548 _30549 P m x i h1 h2). Qed.
Lemma lem2748677 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term132 A i m P) (h2 : (m x) = i) : term323 A m P y x.
Proof. exact (@lem2748676 A (term276 A m y x) (y x) P m x i h1 h2). Qed.
Lemma lem2748680 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : term324 A P y x.
Proof. exact (@lem2748677 A y P m x i h3 h5 (@lem2748673 A y m P x h1 h2 h4)). Qed.
Lemma lem2748681 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : term325 A P y x.
Proof. exact (fun h0 : term251 A P y x => @lem2748680 A y P m x i h1 h2 h3 h4 h5). Qed.
Lemma lem2748683 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2748684 {A : Type'} (P : A -> Prop) (y : A -> A) (x : A) : (term325 A P y x) = (term324 A P y x).
Proof. exact (@lem2748683 (term324 A P y x)). Qed.
Lemma lem2748685 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : term324 A P y x.
Proof. exact (EQ_MP (@lem2748684 A P y x) (@lem2748681 A y P m x i h1 h2 h3 h4 h5)). Qed.
Lemma lem2748691 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2748692 {A : Type'} (P : A -> Prop) (y : A -> A) (_30550 : A) : (term265 A y P _30550) = (term326 A P y _30550).
Proof. exact (@lem2748691 (P _30550) (term251 A P y _30550)). Qed.
Lemma lem2748698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2748699 {A : Type'} (P : A -> Prop) (y : A -> A) (_30550 : A) : (term327 A y P _30550) = (term328 A P y _30550).
Proof. exact (MK_COMB (@lem2748698) (@lem2748692 A P y _30550)). Qed.
Lemma lem2748705 {A : Type'} (P : A -> Prop) (y : A -> A) (_30550 : A) : (term326 A P y _30550) = (term326 A P y _30550).
Proof. exact (eq_refl (term326 A P y _30550)). Qed.
Lemma lem2748706 {A : Type'} (P : A -> Prop) (y : A -> A) (_30550 : A) : ((term265 A y P _30550) = (term326 A P y _30550)) = ((term326 A P y _30550) = (term326 A P y _30550)).
Proof. exact (MK_COMB (@lem2748699 A P y _30550) (@lem2748705 A P y _30550)). Qed.
Lemma lem2748708 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2748709 (x : Prop) : (x = x) = True.
Proof. exact (@lem2748708 Prop x). Qed.
Lemma lem2748710 {A : Type'} (P : A -> Prop) (y : A -> A) (_30550 : A) : ((term326 A P y _30550) = (term326 A P y _30550)) = True.
Proof. exact (@lem2748709 (term326 A P y _30550)). Qed.
Lemma lem2748711 {A : Type'} (P : A -> Prop) (y : A -> A) (_30550 : A) : ((term265 A y P _30550) = (term326 A P y _30550)) = True.
Proof. exact (TRANS (@lem2748706 A P y _30550) (@lem2748710 A P y _30550)). Qed.
Lemma lem2748712 {A : Type'} (P : A -> Prop) (y : A -> A) (_30550 : A) : True = ((term265 A y P _30550) = (term326 A P y _30550)).
Proof. exact (SYM (@lem2748711 A P y _30550)). Qed.
Lemma lem2748713 {A : Type'} (P : A -> Prop) (y : A -> A) (_30550 : A) : (term265 A y P _30550) = (term326 A P y _30550).
Proof. exact (EQ_MP (@lem2748712 A P y _30550) (@lem0)). Qed.
Lemma lem2748714 {A : Type'} (_30550 : A) (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term326 A P y _30550.
Proof. exact (EQ_MP (@lem2748713 A P y _30550) (@lem2748310 A _30550 m y P h1)). Qed.
Lemma lem2748716 (b : Prop) (a : Prop) : (a \/ b) = (term272 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2748717 {A : Type'} (y : A -> A) (P : A -> Prop) (_30550 : A) : (term326 A P y _30550) = (term329 A y P _30550).
Proof. exact (@lem2748716 (term251 A P y _30550) (P _30550)). Qed.
Lemma lem2748719 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2748720 {A : Type'} (P : A -> Prop) (y : A -> A) (_30550 : A) : (term330 A P y _30550) = (term324 A P y _30550).
Proof. exact (@lem2748719 (term324 A P y _30550)). Qed.
Lemma lem2748721 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2748722 {A : Type'} (P : A -> Prop) (y : A -> A) (_30550 : A) : (term331 A P y _30550) = (term332 A P y _30550).
Proof. exact (MK_COMB (@lem2748721) (@lem2748720 A P y _30550)). Qed.
Lemma lem2748723 {A : Type'} (P : A -> Prop) (_30550 : A) : (P _30550) = (P _30550).
Proof. exact (eq_refl (P _30550)). Qed.
Lemma lem2748724 {A : Type'} (y : A -> A) (P : A -> Prop) (_30550 : A) : (term329 A y P _30550) = (term333 A y P _30550).
Proof. exact (MK_COMB (@lem2748722 A P y _30550) (@lem2748723 A P _30550)). Qed.
Lemma lem2748725 {A : Type'} (y : A -> A) (P : A -> Prop) (_30550 : A) : (term326 A P y _30550) = (term333 A y P _30550).
Proof. exact (TRANS (@lem2748717 A y P _30550) (@lem2748724 A y P _30550)). Qed.
Lemma lem2748728 {A : Type'} (_30550 : A) (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term333 A y P _30550.
Proof. exact (EQ_MP (@lem2748725 A y P _30550) (@lem2748714 A _30550 m y P h1)). Qed.
Lemma lem2748729 {A : Type'} (_30550 : A) (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term333 A y P _30550.
Proof. exact (@lem2748728 A _30550 m y P h1). Qed.
Lemma lem2748730 {A : Type'} (x : A) (m : A -> int) (y : A -> A) (P : A -> Prop) (h1 : term202 A m y P) : term333 A y P x.
Proof. exact (@lem2748729 A x m y P h1). Qed.
Lemma lem2748733 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : P x.
Proof. exact (@lem2748730 A x m y P h1 (@lem2748685 A y P m x i h1 h2 h3 h4 h5)). Qed.
Lemma lem2748734 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : (m x) = i) : term334 A P x.
Proof. exact (fun h0 : term143 A P x => @lem2748733 A y P m x i h1 h2 h3 h0 h4). Qed.
Lemma lem2748736 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2748737 {A : Type'} (P : A -> Prop) (x : A) : (term334 A P x) = (P x).
Proof. exact (@lem2748736 (P x)). Qed.
Lemma lem2748738 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : (m x) = i) : P x.
Proof. exact (EQ_MP (@lem2748737 A P x) (@lem2748734 A y P m x i h1 h2 h3 h4)). Qed.
Lemma lem2748741 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2748743 {A : Type'} (P : A -> Prop) (x : A) : (term143 A P x) = (term335 A P x).
Proof. exact (@lem2748741 (P x)). Qed.
Lemma lem2748746 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term335 A P x.
Proof. exact (EQ_MP (@lem2748743 A P x) (@lem2748282 A P x h1)). Qed.
Lemma lem2748749 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (@lem2748746 A P x h4 (@lem2748738 A y P m x i h1 h2 h3 h5)). Qed.
Lemma lem2748750 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : term336.
Proof. exact (fun h0 : ~ False => @lem2748749 A y P m x i h1 h2 h3 h4 h5). Qed.
Lemma lem2748752 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2748753 : term336 = False.
Proof. exact (@lem2748752 False). Qed.
Lemma lem2748754 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748753) (@lem2748750 A y P m x i h1 h2 h3 h4 h5)). Qed.
Lemma lem2748755 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : (term143 A P x) = False.
Proof. exact (prop_ext (fun h6 : term143 A P x => @lem2748754 A y P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2748282 A P x h4)). Qed.
Lemma lem2748757 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748755 A y P m x i h1 h2 h3 h4 h5) (@lem2748282 A P x h4)). Qed.
Lemma lem2748758 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : (term143 A P x) = False.
Proof. exact (prop_ext (fun h6 : term143 A P x => @lem2748757 A y P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2748201 A P x h4)). Qed.
Lemma lem2748759 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748758 A y P m x i h1 h2 h3 h4 h5) (@lem2748201 A P x h4)). Qed.
Lemma lem2748760 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : ((m x) = i) = False.
Proof. exact (prop_ext (fun h6 : (m x) = i => @lem2748759 A y P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2748199 A m x i h5)). Qed.
Lemma lem2748761 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748760 A y P m x i h1 h2 h3 h4 h5) (@lem2748199 A m x i h5)). Qed.
Lemma lem2748762 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : (term143 A P x) = False.
Proof. exact (prop_ext (fun h6 : term143 A P x => @lem2748761 A y P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2748142 A P x h4)). Qed.
Lemma lem2748763 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748762 A y P m x i h1 h2 h3 h4 h5) (@lem2748142 A P x h4)). Qed.
Lemma lem2748764 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : ((m x) = i) = False.
Proof. exact (prop_ext (fun h6 : (m x) = i => @lem2748763 A y P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2748138 A m x i h5)). Qed.
Lemma lem2748765 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748764 A y P m x i h1 h2 h3 h4 h5) (@lem2748138 A m x i h5)). Qed.
Lemma lem2748766 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : (term143 A P x) = False.
Proof. exact (prop_ext (fun h6 : term143 A P x => @lem2748765 A y P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2748142 A P x h4)). Qed.
Lemma lem2748767 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748766 A y P m x i h1 h2 h3 h4 h5) (@lem2748142 A P x h4)). Qed.
Lemma lem2748768 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : ((m x) = i) = False.
Proof. exact (prop_ext (fun h6 : (m x) = i => @lem2748767 A y P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2748138 A m x i h5)). Qed.
Lemma lem2748769 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748768 A y P m x i h1 h2 h3 h4 h5) (@lem2748138 A m x i h5)). Qed.
Lemma lem2748770 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : (term23 A m) = False.
Proof. exact (prop_ext (fun h6 : term23 A m => @lem2748769 A y P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2748057 A m h2)). Qed.
Lemma lem2748771 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748770 A y P m x i h1 h2 h3 h4 h5) (@lem2748057 A m h2)). Qed.
Lemma lem2748772 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : (term202 A m y P) = False.
Proof. exact (prop_ext (fun h6 : term202 A m y P => @lem2748771 A y P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2748050 A m y P h1)). Qed.
Lemma lem2748773 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748772 A y P m x i h1 h2 h3 h4 h5) (@lem2748050 A m y P h1)). Qed.
Lemma lem2748774 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : (term143 A P x) = False.
Proof. exact (prop_ext (fun h6 : term143 A P x => @lem2748773 A y P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2748019 A P x h4)). Qed.
Lemma lem2748775 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748774 A y P m x i h1 h2 h3 h4 h5) (@lem2748019 A P x h4)). Qed.
Lemma lem2748776 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : ((m x) = i) = False.
Proof. exact (prop_ext (fun h6 : (m x) = i => @lem2748775 A y P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2748013 A m x i h5)). Qed.
Lemma lem2748777 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748776 A y P m x i h1 h2 h3 h4 h5) (@lem2748013 A m x i h5)). Qed.
Lemma lem2748778 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : (term23 A m) = False.
Proof. exact (prop_ext (fun h6 : term23 A m => @lem2748777 A y P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2747949 A m h2)). Qed.
Lemma lem2748779 {A : Type'} (y : A -> A) (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term202 A m y P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748778 A y P m x i h1 h2 h3 h4 h5) (@lem2747949 A m h2)). Qed.
Lemma lem2748780 {A : Type'} (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (ex_elim (@lem2747805 A m P h1) (fun y : A -> A => fun h0 : term204 A m P y => @lem2748779 A y P m x i h0 h2 h3 h4 h5)). Qed.
Lemma lem2748781 {A : Type'} (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : (term143 A P x) = False.
Proof. exact (prop_ext (fun h6 : term143 A P x => @lem2748780 A P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2747933 A P x h4)). Qed.
Lemma lem2748782 {A : Type'} (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748781 A P m x i h1 h2 h3 h4 h5) (@lem2747933 A P x h4)). Qed.
Lemma lem2748783 {A : Type'} (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : ((m x) = i) = False.
Proof. exact (prop_ext (fun h6 : (m x) = i => @lem2748782 A P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2747927 A m x i h5)). Qed.
Lemma lem2748784 {A : Type'} (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748783 A P m x i h1 h2 h3 h4 h5) (@lem2747927 A m x i h5)). Qed.
Lemma lem2748785 {A : Type'} (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : (term23 A m) = False.
Proof. exact (prop_ext (fun h6 : term23 A m => @lem2748784 A P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2747637 A m h2)). Qed.
Lemma lem2748786 {A : Type'} (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748785 A P m x i h1 h2 h3 h4 h5) (@lem2747637 A m h2)). Qed.
Lemma lem2748787 {A : Type'} (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : (term143 A P x) = False.
Proof. exact (prop_ext (fun h6 : term143 A P x => @lem2748786 A P m x i h1 h2 h3 h4 h5) (fun h6 : False => @lem2747624 A P x h4)). Qed.
Lemma lem2748788 {A : Type'} (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : term143 A P x) (h5 : (m x) = i) : False.
Proof. exact (EQ_MP (@lem2748787 A P m x i h1 h2 h3 h4 h5) (@lem2747624 A P x h4)). Qed.
Lemma lem2748789 {A : Type'} (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : (m x) = i) : term142 A P x.
Proof. exact (fun h0 : term143 A P x => @lem2748788 A P m x i h1 h2 h3 h0 h4). Qed.
Lemma lem2748790 {A : Type'} (P : A -> Prop) (m : A -> int) (x : A) (i : int) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term132 A i m P) (h4 : (m x) = i) : P x.
Proof. exact (EQ_MP (@lem2747623 A P x) (@lem2748789 A P m x i h1 h2 h3 h4)). Qed.
Lemma lem2748791 {A : Type'} (x : A) (i : int) (m : A -> int) (P : A -> Prop) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term132 A i m P) : term126 A m i P x.
Proof. exact (fun h0 : (m x) = i => @lem2748790 A P m x i h1 h2 h3 h0). Qed.
Lemma lem2748796 {A : Type'} (i : int) (m : A -> int) (P : A -> Prop) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term132 A i m P) : term94 A m i P.
Proof. exact (fun x : A => @lem2748791 A x i m P h1 h2 h3). Qed.
Lemma lem2748797 {A : Type'} (i : int) (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term80 A m i P.
Proof. exact (fun h0 : term132 A i m P => @lem2748796 A i m P h1 h2 h0). Qed.
Lemma lem2748798 {A : Type'} (i : int) (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term82 A m i P.
Proof. exact (fun h0 : term215 i => @lem2748797 A i P m h1 h2). Qed.
Lemma lem2748803 {A : Type'} (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term85 A m P.
Proof. exact (fun i : int => @lem2748798 A i P m h1 h2). Qed.
Lemma lem2748804 {A : Type'} (P : A -> Prop) (m : A -> int) (h1 : term23 A m) : term115 A m P.
Proof. exact (fun h0 : term22 A m P => @lem2748803 A P m h0 h1). Qed.
Lemma lem2748805 {A : Type'} (m : A -> int) (P : A -> Prop) : term117 A m P.
Proof. exact (fun h0 : term23 A m => @lem2748804 A P m h0). Qed.
Lemma lem2748810 {A : Type'} (P : A -> Prop) : term121 A P.
Proof. exact (fun m : A -> int => @lem2748805 A m P). Qed.
Lemma lem2748815 {A : Type'} : term125 A.
Proof. exact (fun P : A -> Prop => @lem2748810 A P). Qed.
Lemma lem2748816 {A : Type'} : term124 A.
Proof. exact (EQ_MP (@lem2747614 A) (@lem2748815 A)). Qed.
Lemma lem2748817 {A : Type'} (P : A -> Prop) : term337 A P.
Proof. exact (@lem2748816 A P). Qed.
Lemma lem2748818 {A : Type'} (P : A -> Prop) : (term337 A P) = (term120 A P).
Proof. exact (eq_refl (term337 A P)). Qed.
Lemma lem2748819 {A : Type'} (P : A -> Prop) : term120 A P.
Proof. exact (EQ_MP (@lem2748818 A P) (@lem2748817 A P)). Qed.
Lemma lem2748820 {A : Type'} (P : A -> Prop) (m : A -> int) : term338 A P m.
Proof. exact (@lem2748819 A P m). Qed.
Lemma lem2748821 {A : Type'} (m : A -> int) (P : A -> Prop) : (term338 A P m) = (term107 A m P).
Proof. exact (eq_refl (term338 A P m)). Qed.
Lemma lem2748822 {A : Type'} (m : A -> int) (P : A -> Prop) : term107 A m P.
Proof. exact (EQ_MP (@lem2748821 A m P) (@lem2748820 A P m)). Qed.
Lemma lem2748824 {A : Type'} (m : A -> int) (P : A -> Prop) : term107 A m P.
Proof. exact (@lem2747379 A m P (@lem2748822 A m P)). Qed.
Lemma lem2748825 {A : Type'} (P : A -> Prop) (m : A -> int) (h1 : term23 A m) : term114 A m P.
Proof. exact (@lem2748824 A m P (@lem2747082 A m h1)). Qed.
Lemma lem2748826 {A : Type'} (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term105 A m P.
Proof. exact (@lem2748825 A P m h2 (@lem2747081 A m P h1)). Qed.
Lemma lem2748827 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term106 A m P) : False.
Proof. exact (@lem2748826 A P m h1 h2 (@lem2747363 A m P h3)). Qed.
Lemma lem2748828 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term106 A m P) : (term106 A m P) = False.
Proof. exact (prop_ext (fun h4 : term106 A m P => @lem2748827 A m P h1 h2 h3) (fun h4 : False => @lem2747363 A m P h3)). Qed.
Lemma lem2748829 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term106 A m P) : False.
Proof. exact (EQ_MP (@lem2748828 A m P h1 h2 h3) (@lem2747363 A m P h3)). Qed.
Lemma lem2748830 {A : Type'} (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term105 A m P.
Proof. exact (fun h0 : term106 A m P => @lem2748829 A m P h1 h2 h0). Qed.
Lemma lem2748831 {A : Type'} (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term85 A m P.
Proof. exact (EQ_MP (@lem2747362 A m P) (@lem2748830 A P m h1 h2)). Qed.
Lemma lem2748833 (p : Prop) : p = (term104 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2748834 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term103 A m P x) = (term339 A m P x).
Proof. exact (@lem2748833 (term103 A m P x)). Qed.
Lemma lem2748835 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term339 A m P x) = (term103 A m P x).
Proof. exact (SYM (@lem2748834 A m P x)). Qed.
Lemma lem2748836 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term340 A m P x) : term340 A m P x.
Proof. exact (h1). Qed.
Lemma lem2748839 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term341 A m P x) : term341 A m P x.
Proof. exact (h1). Qed.
Lemma lem2748840 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : term342 A m P x.
Proof. exact (fun h0 : term341 A m P x => @lem2748839 A m P x h0). Qed.
Lemma lem2748841 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term342 A m P x) : term342 A m P x.
Proof. exact (h1). Qed.
Lemma lem2748842 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term341 A m P x) : term341 A m P x.
Proof. exact (h1). Qed.
Lemma lem2748843 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term341 A m P x) (h2 : term342 A m P x) : term341 A m P x.
Proof. exact (@lem2748841 A m P x h2 (@lem2748842 A m P x h1)). Qed.
Lemma lem2748844 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term341 A m P x) : term343 A m P x.
Proof. exact (fun h0 : term342 A m P x => @lem2748843 A m P x h1 h0). Qed.
Lemma lem2748845 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term342 A m P x) : term342 A m P x.
Proof. exact (h1). Qed.
Lemma lem2748846 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term341 A m P x) (h2 : term342 A m P x) : term341 A m P x.
Proof. exact (@lem2748844 A m P x h1 (@lem2748845 A m P x h2)). Qed.
Lemma lem2748847 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term342 A m P x) : term342 A m P x.
Proof. exact (fun h0 : term341 A m P x => @lem2748846 A m P x h0 h1). Qed.
Lemma lem2748848 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : term344 A m P x.
Proof. exact (fun h0 : term342 A m P x => @lem2748847 A m P x h0). Qed.
Lemma lem2748851 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : term342 A m P x.
Proof. exact (@lem2748848 A m P x (@lem2748840 A m P x)). Qed.
Lemma lem2748852 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : term342 A m P x.
Proof. exact (@lem2748851 A m P x). Qed.
Lemma lem2748886 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2748887 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term339 A m P x) = (term345 A m P x).
Proof. exact (@lem2748886 (term340 A m P x)). Qed.
Lemma lem2748889 (t : Prop) : (term112 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2748890 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term345 A m P x) = (term103 A m P x).
Proof. exact (@lem2748889 (term103 A m P x)). Qed.
Lemma lem2748893 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term339 A m P x) = (term103 A m P x).
Proof. exact (TRANS (@lem2748887 A m P x) (@lem2748890 A m P x)). Qed.
Lemma lem2748906 {A : Type'} (m : A -> int) (P : A -> Prop) : (term113 A m P) = (term113 A m P).
Proof. exact (eq_refl (term113 A m P)). Qed.
Lemma lem2748907 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term346 A m P x) = (term347 A m P x).
Proof. exact (MK_COMB (@lem2748906 A m P) (@lem2748893 A m P x)). Qed.
Lemma lem2748910 {A : Type'} (m : A -> int) : (term116 A m) = (term116 A m).
Proof. exact (eq_refl (term116 A m)). Qed.
Lemma lem2748911 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term341 A m P x) = (term348 A m P x).
Proof. exact (MK_COMB (@lem2748910 A m) (@lem2748907 A m P x)). Qed.
Lemma lem2748914 {A : Type'} (P : A -> Prop) (x : A) : (term349 A P x) = (term350 A P x).
Proof. exact (fun_ext (fun m : A -> int => @lem2748911 A m P x)). Qed.
Lemma lem2748915 {A : Type'} : (@all (A -> int)) = (@all (A -> int)).
Proof. exact (eq_refl (@all (A -> int))). Qed.
Lemma lem2748916 {A : Type'} (P : A -> Prop) (x : A) : (term351 A P x) = (term352 A P x).
Proof. exact (MK_COMB (@lem2748915 A) (@lem2748914 A P x)). Qed.
Lemma lem2748921 {A : Type'} (x : A) : (term353 A x) = (term354 A x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem2748916 A P x)). Qed.
Lemma lem2748922 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem2748923 {A : Type'} (x : A) : (term355 A x) = (term356 A x).
Proof. exact (MK_COMB (@lem2748922 A) (@lem2748921 A x)). Qed.
Lemma lem2748928 {A : Type'} : (term357 A) = (term358 A).
Proof. exact (fun_ext (fun x : A => @lem2748923 A x)). Qed.
Lemma lem2748929 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748938 {A : Type'} : (term359 A) = (term360 A).
Proof. exact (MK_COMB (@lem2748929 A) (@lem2748928 A)). Qed.
Lemma lem2748939 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2748944 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) (x : A) : (term126 A m i P x) = (term126 A m i P x).
Proof. exact (eq_refl (term126 A m i P x)). Qed.
Lemma lem2748945 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term127 A m i P) = (term127 A m i P).
Proof. exact (fun_ext (fun x : A => @lem2748944 A m i P x)). Qed.
Lemma lem2748946 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748947 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term94 A m i P) = (term94 A m i P).
Proof. exact (MK_COMB (@lem2748946 A) (@lem2748945 A m i P)). Qed.
Lemma lem2748950 (i : int) : (term62 i) = (term62 i).
Proof. exact (eq_refl (term62 i)). Qed.
Lemma lem2748951 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term96 A m i P) = (term96 A m i P).
Proof. exact (MK_COMB (@lem2748950 i) (@lem2748947 A m i P)). Qed.
Lemma lem2748952 {A : Type'} (m : A -> int) (P : A -> Prop) : (term98 A m P) = (term98 A m P).
Proof. exact (fun_ext (fun i : int => @lem2748951 A m i P)). Qed.
Lemma lem2748953 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2748954 {A : Type'} (m : A -> int) (P : A -> Prop) : (term99 A m P) = (term99 A m P).
Proof. exact (MK_COMB (@lem2748953) (@lem2748952 A m P)). Qed.
Lemma lem2748955 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2748956 {A : Type'} (m : A -> int) (P : A -> Prop) : (term101 A m P) = (term101 A m P).
Proof. exact (MK_COMB (@lem2748955) (@lem2748954 A m P)). Qed.
Lemma lem2748957 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term103 A m P x) = (term103 A m P x).
Proof. exact (MK_COMB (@lem2748956 A m P) (@lem2748939 A P x)). Qed.
Lemma lem2748958 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2748963 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term134 A m x P y) = (term134 A m x P y).
Proof. exact (eq_refl (term134 A m x P y)). Qed.
Lemma lem2748964 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term135 A m x P) = (term135 A m x P).
Proof. exact (fun_ext (fun y : A => @lem2748963 A m x P y)). Qed.
Lemma lem2748965 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748966 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term136 A m x P) = (term136 A m x P).
Proof. exact (MK_COMB (@lem2748965 A) (@lem2748964 A m x P)). Qed.
Lemma lem2748967 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2748968 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term137 A m x P) = (term137 A m x P).
Proof. exact (MK_COMB (@lem2748967) (@lem2748966 A m x P)). Qed.
Lemma lem2748969 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term138 A m P x) = (term138 A m P x).
Proof. exact (MK_COMB (@lem2748968 A m x P) (@lem2748958 A P x)). Qed.
Lemma lem2748970 {A : Type'} (m : A -> int) (P : A -> Prop) : (term139 A m P) = (term139 A m P).
Proof. exact (fun_ext (fun x : A => @lem2748969 A m P x)). Qed.
Lemma lem2748971 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748972 {A : Type'} (m : A -> int) (P : A -> Prop) : (term22 A m P) = (term22 A m P).
Proof. exact (MK_COMB (@lem2748971 A) (@lem2748970 A m P)). Qed.
Lemma lem2748973 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2748974 {A : Type'} (m : A -> int) (P : A -> Prop) : (term113 A m P) = (term113 A m P).
Proof. exact (MK_COMB (@lem2748973) (@lem2748972 A m P)). Qed.
Lemma lem2748975 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term347 A m P x) = (term347 A m P x).
Proof. exact (MK_COMB (@lem2748974 A m P) (@lem2748957 A m P x)). Qed.
Lemma lem2748976 {A : Type'} (m : A -> int) (x : A) : (term140 A m x) = (term140 A m x).
Proof. exact (eq_refl (term140 A m x)). Qed.
Lemma lem2748977 {A : Type'} (m : A -> int) : (term141 A m) = (term141 A m).
Proof. exact (fun_ext (fun x : A => @lem2748976 A m x)). Qed.
Lemma lem2748978 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748979 {A : Type'} (m : A -> int) : (term23 A m) = (term23 A m).
Proof. exact (MK_COMB (@lem2748978 A) (@lem2748977 A m)). Qed.
Lemma lem2748980 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2748981 {A : Type'} (m : A -> int) : (term116 A m) = (term116 A m).
Proof. exact (MK_COMB (@lem2748980) (@lem2748979 A m)). Qed.
Lemma lem2748982 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term348 A m P x) = (term348 A m P x).
Proof. exact (MK_COMB (@lem2748981 A m) (@lem2748975 A m P x)). Qed.
Lemma lem2748983 {A : Type'} (P : A -> Prop) (x : A) : (term350 A P x) = (term350 A P x).
Proof. exact (fun_ext (fun m : A -> int => @lem2748982 A m P x)). Qed.
Lemma lem2748984 {A : Type'} : (@all (A -> int)) = (@all (A -> int)).
Proof. exact (eq_refl (@all (A -> int))). Qed.
Lemma lem2748985 {A : Type'} (P : A -> Prop) (x : A) : (term352 A P x) = (term352 A P x).
Proof. exact (MK_COMB (@lem2748984 A) (@lem2748983 A P x)). Qed.
Lemma lem2748986 {A : Type'} (x : A) : (term354 A x) = (term354 A x).
Proof. exact (fun_ext (fun P : A -> Prop => @lem2748985 A P x)). Qed.
Lemma lem2748987 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem2748988 {A : Type'} (x : A) : (term356 A x) = (term356 A x).
Proof. exact (MK_COMB (@lem2748987 A) (@lem2748986 A x)). Qed.
Lemma lem2748989 {A : Type'} : (term358 A) = (term358 A).
Proof. exact (fun_ext (fun x : A => @lem2748988 A x)). Qed.
Lemma lem2748990 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2748991 {A : Type'} : (term360 A) = (term360 A).
Proof. exact (MK_COMB (@lem2748990 A) (@lem2748989 A)). Qed.
Lemma lem2749056 {A : Type'} : (term359 A) = (term360 A).
Proof. exact (TRANS (@lem2748938 A) (@lem2748991 A)). Qed.
Lemma lem2749057 {A : Type'} : (term360 A) = (term359 A).
Proof. exact (SYM (@lem2749056 A)). Qed.
Lemma lem2749058 {A : Type'} (m : A -> int) (h1 : term23 A m) : term23 A m.
Proof. exact (h1). Qed.
Lemma lem2749059 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term22 A m P) : term22 A m P.
Proof. exact (h1). Qed.
Lemma lem2749060 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term99 A m P) : term99 A m P.
Proof. exact (h1). Qed.
Lemma lem2749062 (p : Prop) : p = (term104 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2749063 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (term142 A P x).
Proof. exact (@lem2749062 (P x)). Qed.
Lemma lem2749064 {A : Type'} (P : A -> Prop) (x : A) : (term142 A P x) = (P x).
Proof. exact (SYM (@lem2749063 A P x)). Qed.
Lemma lem2749065 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term143 A P x.
Proof. exact (h1). Qed.
Lemma lem2749066 {A : Type'} (m : A -> int) (x : A) : (term140 A m x) = (term140 A m x).
Proof. exact (eq_refl (term140 A m x)). Qed.
Lemma lem2749067 {A : Type'} (m : A -> int) : (term141 A m) = (term141 A m).
Proof. exact (fun_ext (fun x : A => @lem2749066 A m x)). Qed.
Lemma lem2749068 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2749077 {A : Type'} (m : A -> int) : (term23 A m) = (term23 A m).
Proof. exact (MK_COMB (@lem2749068 A) (@lem2749067 A m)). Qed.
Lemma lem2749078 {A : Type'} (m : A -> int) (h1 : term23 A m) : term23 A m.
Proof. exact (EQ_MP (@lem2749077 A m) (@lem2749058 A m h1)). Qed.
Lemma lem2749085 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term144 A m x P y) = (term145 A m x P y).
Proof. exact (@lem17362 (term146 A y m x) (P y)). Qed.
Lemma lem2749086 {A : Type'} (P : A -> Prop) : (term147 A P) = (term148 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem2749087 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term149 A m x P) = (term150 A m x P).
Proof. exact (@lem2749086 A (term135 A m x P)). Qed.
Lemma lem2749088 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term151 A m x P y) = (term134 A m x P y).
Proof. exact (eq_refl (term151 A m x P y)). Qed.
Lemma lem2749089 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2749090 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term152 A m x P y) = (term144 A m x P y).
Proof. exact (MK_COMB (@lem2749089) (@lem2749088 A m x P y)). Qed.
Lemma lem2749091 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term152 A m x P y) = (term145 A m x P y).
Proof. exact (TRANS (@lem2749090 A m x P y) (@lem2749085 A m x P y)). Qed.
Lemma lem2749092 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term153 A m x P) = (term154 A m x P).
Proof. exact (fun_ext (fun y : A => @lem2749091 A m x P y)). Qed.
Lemma lem2749093 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2749094 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term150 A m x P) = (term155 A m x P).
Proof. exact (MK_COMB (@lem2749093 A) (@lem2749092 A m x P)). Qed.
Lemma lem2749095 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term149 A m x P) = (term155 A m x P).
Proof. exact (TRANS (@lem2749087 A m x P) (@lem2749094 A m x P)). Qed.
Lemma lem2749096 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2749097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2749098 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term156 A m x P) = (term157 A m x P).
Proof. exact (MK_COMB (@lem2749097) (@lem2749095 A m x P)). Qed.
Lemma lem2749099 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term158 A m P x) = (term159 A m P x).
Proof. exact (MK_COMB (@lem2749098 A m x P) (@lem2749096 A P x)). Qed.
Lemma lem2749100 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term138 A m P x) = (term158 A m P x).
Proof. exact (@lem17265 (term136 A m x P) (P x)). Qed.
Lemma lem2749101 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term138 A m P x) = (term159 A m P x).
Proof. exact (TRANS (@lem2749100 A m P x) (@lem2749099 A m P x)). Qed.
Lemma lem2749102 {A : Type'} (m : A -> int) (P : A -> Prop) : (term139 A m P) = (term160 A m P).
Proof. exact (fun_ext (fun x : A => @lem2749101 A m P x)). Qed.
Lemma lem2749103 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2749104 {A : Type'} (m : A -> int) (P : A -> Prop) : (term22 A m P) = (term161 A m P).
Proof. exact (MK_COMB (@lem2749103 A) (@lem2749102 A m P)). Qed.
Lemma lem2749187 {A : Type'} (P : A -> Prop) (Q : Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem2749188 {A : Type'} (P : A -> Prop) (Q : Prop) : (term162 A P Q) = (term163 A P Q).
Proof. exact (@lem2749187 A P Q). Qed.
Lemma lem2749189 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term164 A m P x) = (term165 A m P x).
Proof. exact (@lem2749188 A (term154 A m x P) (P x)). Qed.
Lemma lem2749190 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term166 A m x P y) = (term145 A m x P y).
Proof. exact (eq_refl (term166 A m x P y)). Qed.
Lemma lem2749191 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term167 A m x P) = (term154 A m x P).
Proof. exact (fun_ext (fun y : A => @lem2749190 A m x P y)). Qed.
Lemma lem2749192 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2749193 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term168 A m x P) = (term155 A m x P).
Proof. exact (MK_COMB (@lem2749192 A) (@lem2749191 A m x P)). Qed.
Lemma lem2749194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2749195 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) : (term169 A m x P) = (term157 A m x P).
Proof. exact (MK_COMB (@lem2749194) (@lem2749193 A m x P)). Qed.
Lemma lem2749196 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2749197 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term164 A m P x) = (term159 A m P x).
Proof. exact (MK_COMB (@lem2749195 A m x P) (@lem2749196 A P x)). Qed.
Lemma lem2749198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2749199 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term170 A m P x) = (term171 A m P x).
Proof. exact (MK_COMB (@lem2749198) (@lem2749197 A m P x)). Qed.
Lemma lem2749200 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term166 A m x P y) = (term145 A m x P y).
Proof. exact (eq_refl (term166 A m x P y)). Qed.
Lemma lem2749201 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2749202 {A : Type'} (m : A -> int) (x : A) (P : A -> Prop) (y : A) : (term172 A m x P y) = (term173 A m x P y).
Proof. exact (MK_COMB (@lem2749201) (@lem2749200 A m x P y)). Qed.
Lemma lem2749203 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem2749204 {A : Type'} (m : A -> int) (y : A) (P : A -> Prop) (x : A) : (term174 A m y P x) = (term175 A m y P x).
Proof. exact (MK_COMB (@lem2749202 A m x P y) (@lem2749203 A P x)). Qed.
Lemma lem2749205 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term176 A m P x) = (term177 A m P x).
Proof. exact (fun_ext (fun y : A => @lem2749204 A m y P x)). Qed.
Lemma lem2749206 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2749207 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term165 A m P x) = (term178 A m P x).
Proof. exact (MK_COMB (@lem2749206 A) (@lem2749205 A m P x)). Qed.
Lemma lem2749208 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : ((term164 A m P x) = (term165 A m P x)) = ((term159 A m P x) = (term178 A m P x)).
Proof. exact (MK_COMB (@lem2749199 A m P x) (@lem2749207 A m P x)). Qed.
Lemma lem2749209 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term159 A m P x) = (term178 A m P x).
Proof. exact (EQ_MP (@lem2749208 A m P x) (@lem2749189 A m P x)). Qed.
Lemma lem2749210 {A : Type'} (m : A -> int) (P : A -> Prop) : (term160 A m P) = (term179 A m P).
Proof. exact (fun_ext (fun x : A => @lem2749209 A m P x)). Qed.
Lemma lem2749211 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2749212 {A : Type'} (m : A -> int) (P : A -> Prop) : (term161 A m P) = (term180 A m P).
Proof. exact (MK_COMB (@lem2749211 A) (@lem2749210 A m P)). Qed.
Lemma lem2749214 {A B : Type'} (P : type1413 A B) : (term181 A B P) = (term182 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem2749215 {A : Type'} (P : type1402 A) : (term183 A P) = (term184 A P).
Proof. exact (@lem2749214 A A P). Qed.
Lemma lem2749216 {A : Type'} (m : A -> int) (P : A -> Prop) : (term185 A m P) = (term186 A m P).
Proof. exact (@lem2749215 A (term187 A m P)). Qed.
Lemma lem2749217 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term188 A m P x) = (term177 A m P x).
Proof. exact (eq_refl (term188 A m P x)). Qed.
Lemma lem2749218 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2749219 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (y : A) : (term189 A m P x y) = (term190 A m P x y).
Proof. exact (MK_COMB (@lem2749217 A m P x) (@lem2749218 A y)). Qed.
Lemma lem2749220 {A : Type'} (m : A -> int) (y : A) (P : A -> Prop) (x : A) : (term190 A m P x y) = (term175 A m y P x).
Proof. exact (eq_refl (term190 A m P x y)). Qed.
Lemma lem2749221 {A : Type'} (m : A -> int) (y : A) (P : A -> Prop) (x : A) : (term189 A m P x y) = (term175 A m y P x).
Proof. exact (TRANS (@lem2749219 A m P x y) (@lem2749220 A m y P x)). Qed.
Lemma lem2749222 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term191 A m P x) = (term177 A m P x).
Proof. exact (fun_ext (fun y : A => @lem2749221 A m y P x)). Qed.
Lemma lem2749223 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem2749224 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term192 A m P x) = (term178 A m P x).
Proof. exact (MK_COMB (@lem2749223 A) (@lem2749222 A m P x)). Qed.
Lemma lem2749225 {A : Type'} (m : A -> int) (P : A -> Prop) : (term193 A m P) = (term179 A m P).
Proof. exact (fun_ext (fun x : A => @lem2749224 A m P x)). Qed.
Lemma lem2749226 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2749227 {A : Type'} (m : A -> int) (P : A -> Prop) : (term185 A m P) = (term180 A m P).
Proof. exact (MK_COMB (@lem2749226 A) (@lem2749225 A m P)). Qed.
Lemma lem2749228 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2749229 {A : Type'} (m : A -> int) (P : A -> Prop) : (term194 A m P) = (term195 A m P).
Proof. exact (MK_COMB (@lem2749228) (@lem2749227 A m P)). Qed.
Lemma lem2749230 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term188 A m P x) = (term177 A m P x).
Proof. exact (eq_refl (term188 A m P x)). Qed.
Lemma lem2749231 {A : Type'} (y : A -> A) (x : A) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem2749232 {A : Type'} (m : A -> int) (P : A -> Prop) (y : A -> A) (x : A) : (term196 A m P y x) = (term197 A m P y x).
Proof. exact (MK_COMB (@lem2749230 A m P x) (@lem2749231 A y x)). Qed.
Lemma lem2749233 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (x : A) : (term197 A m P y x) = (term198 A m y P x).
Proof. exact (eq_refl (term197 A m P y x)). Qed.
Lemma lem2749234 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) (x : A) : (term196 A m P y x) = (term198 A m y P x).
Proof. exact (TRANS (@lem2749232 A m P y x) (@lem2749233 A m y P x)). Qed.
Lemma lem2749235 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) : (term199 A m P y) = (term200 A m y P).
Proof. exact (fun_ext (fun x : A => @lem2749234 A m y P x)). Qed.
Lemma lem2749236 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2749237 {A : Type'} (m : A -> int) (y : A -> A) (P : A -> Prop) : (term201 A m P y) = (term202 A m y P).
Proof. exact (MK_COMB (@lem2749236 A) (@lem2749235 A m y P)). Qed.
Lemma lem2749238 {A : Type'} (m : A -> int) (P : A -> Prop) : (term203 A m P) = (term204 A m P).
Proof. exact (fun_ext (fun y : A -> A => @lem2749237 A m y P)). Qed.
Lemma lem2749239 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem2749240 {A : Type'} (m : A -> int) (P : A -> Prop) : (term186 A m P) = (term205 A m P).
Proof. exact (MK_COMB (@lem2749239 A) (@lem2749238 A m P)). Qed.
Lemma lem2749241 {A : Type'} (m : A -> int) (P : A -> Prop) : ((term185 A m P) = (term186 A m P)) = ((term180 A m P) = (term205 A m P)).
Proof. exact (MK_COMB (@lem2749229 A m P) (@lem2749240 A m P)). Qed.
Lemma lem2749242 {A : Type'} (m : A -> int) (P : A -> Prop) : (term180 A m P) = (term205 A m P).
Proof. exact (EQ_MP (@lem2749241 A m P) (@lem2749216 A m P)). Qed.
Lemma lem2749244 {A : Type'} (m : A -> int) (P : A -> Prop) : (term161 A m P) = (term205 A m P).
Proof. exact (TRANS (@lem2749212 A m P) (@lem2749242 A m P)). Qed.
Lemma lem2749245 {A : Type'} (m : A -> int) (P : A -> Prop) : (term22 A m P) = (term205 A m P).
Proof. exact (TRANS (@lem2749104 A m P) (@lem2749244 A m P)). Qed.
Lemma lem2749246 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term22 A m P) : term205 A m P.
Proof. exact (EQ_MP (@lem2749245 A m P) (@lem2749059 A m P h1)). Qed.
Lemma lem2749254 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) (x : A) : (term126 A m i P x) = (term206 A m i P x).
Proof. exact (@lem17265 ((m x) = i) (P x)). Qed.
Lemma lem2749255 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term127 A m i P) = (term207 A m i P).
Proof. exact (fun_ext (fun x : A => @lem2749254 A m i P x)). Qed.
Lemma lem2749256 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2749257 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term94 A m i P) = (term208 A m i P).
Proof. exact (MK_COMB (@lem2749256 A) (@lem2749255 A m i P)). Qed.
Lemma lem2749259 (i : int) : (term212 i) = (term212 i).
Proof. exact (eq_refl (term212 i)). Qed.
Lemma lem2749260 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term361 A m i P) = (term362 A m i P).
Proof. exact (MK_COMB (@lem2749259 i) (@lem2749257 A m i P)). Qed.
Lemma lem2749261 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term96 A m i P) = (term361 A m i P).
Proof. exact (@lem17265 (term215 i) (term94 A m i P)). Qed.
Lemma lem2749262 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term96 A m i P) = (term362 A m i P).
Proof. exact (TRANS (@lem2749261 A m i P) (@lem2749260 A m i P)). Qed.
Lemma lem2749263 {A : Type'} (m : A -> int) (P : A -> Prop) : (term98 A m P) = (term363 A m P).
Proof. exact (fun_ext (fun i : int => @lem2749262 A m i P)). Qed.
Lemma lem2749264 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2749349 {A : Type'} (m : A -> int) (P : A -> Prop) : (term99 A m P) = (term364 A m P).
Proof. exact (MK_COMB (@lem2749264) (@lem2749263 A m P)). Qed.
Lemma lem2749350 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term99 A m P) : term364 A m P.
Proof. exact (EQ_MP (@lem2749349 A m P) (@lem2749060 A m P h1)). Qed.
Lemma lem2749356 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term143 A P x.
Proof. exact (h1). Qed.
Lemma lem2749368 {A : Type'} (m : A -> int) (x : A) : (term140 A m x) = (term140 A m x).
Proof. exact (eq_refl (term140 A m x)). Qed.
Lemma lem2749369 {A : Type'} (m : A -> int) : (term141 A m) = (term141 A m).
Proof. exact (fun_ext (fun x : A => @lem2749368 A m x)). Qed.
Lemma lem2749370 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2749371 {A : Type'} (m : A -> int) : (term23 A m) = (term23 A m).
Proof. exact (MK_COMB (@lem2749370 A) (@lem2749369 A m)). Qed.
Lemma lem2749372 {A : Type'} (m : A -> int) (h1 : term23 A m) : term23 A m.
Proof. exact (EQ_MP (@lem2749371 A m) (@lem2749078 A m h1)). Qed.
Lemma lem2749387 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) (x : A) : (term206 A m i P x) = (term206 A m i P x).
Proof. exact (eq_refl (term206 A m i P x)). Qed.
Lemma lem2749388 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term207 A m i P) = (term207 A m i P).
Proof. exact (fun_ext (fun x : A => @lem2749387 A m i P x)). Qed.
Lemma lem2749389 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2749390 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term208 A m i P) = (term208 A m i P).
Proof. exact (MK_COMB (@lem2749389 A) (@lem2749388 A m i P)). Qed.
Lemma lem2749403 (i : int) : (term212 i) = (term212 i).
Proof. exact (eq_refl (term212 i)). Qed.
Lemma lem2749404 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term362 A m i P) = (term362 A m i P).
Proof. exact (MK_COMB (@lem2749403 i) (@lem2749390 A m i P)). Qed.
Lemma lem2749405 {A : Type'} (m : A -> int) (P : A -> Prop) : (term363 A m P) = (term363 A m P).
Proof. exact (fun_ext (fun i : int => @lem2749404 A m i P)). Qed.
Lemma lem2749406 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2749407 {A : Type'} (m : A -> int) (P : A -> Prop) : (term364 A m P) = (term364 A m P).
Proof. exact (MK_COMB (@lem2749406) (@lem2749405 A m P)). Qed.
Lemma lem2749408 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term99 A m P) : term364 A m P.
Proof. exact (EQ_MP (@lem2749407 A m P) (@lem2749350 A m P h1)). Qed.
Lemma lem2749414 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term143 A P x.
Proof. exact (h1). Qed.
Lemma lem2749447 {A : Type'} (m : A -> int) (x : A) : (term140 A m x) = (term140 A m x).
Proof. exact (eq_refl (term140 A m x)). Qed.
Lemma lem2749448 {A : Type'} (m : A -> int) : (term141 A m) = (term141 A m).
Proof. exact (fun_ext (fun x : A => @lem2749447 A m x)). Qed.
Lemma lem2749449 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2749451 {A : Type'} (m : A -> int) : (term23 A m) = (term23 A m).
Proof. exact (MK_COMB (@lem2749449 A) (@lem2749448 A m)). Qed.
Lemma lem2749452 {A : Type'} (m : A -> int) (h1 : term23 A m) : term23 A m.
Proof. exact (EQ_MP (@lem2749451 A m) (@lem2749372 A m h1)). Qed.
Lemma lem2749454 {A : Type'} (P : Prop) (Q : A -> Prop) : (term218 A P Q) = (term219 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem2749455 {A : Type'} (P : Prop) (Q : A -> Prop) : (term218 A P Q) = (term219 A P Q).
Proof. exact (@lem2749454 A P Q). Qed.
Lemma lem2749456 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term365 A m i P) = (term366 A m i P).
Proof. exact (@lem2749455 A (term236 i) (term207 A m i P)). Qed.
Lemma lem2749457 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) (x : A) : (term223 A m i P x) = (term206 A m i P x).
Proof. exact (eq_refl (term223 A m i P x)). Qed.
Lemma lem2749458 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term224 A m i P) = (term207 A m i P).
Proof. exact (fun_ext (fun x : A => @lem2749457 A m i P x)). Qed.
Lemma lem2749459 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2749460 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term225 A m i P) = (term208 A m i P).
Proof. exact (MK_COMB (@lem2749459 A) (@lem2749458 A m i P)). Qed.
Lemma lem2749461 (i : int) : (term212 i) = (term212 i).
Proof. exact (eq_refl (term212 i)). Qed.
Lemma lem2749462 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term365 A m i P) = (term362 A m i P).
Proof. exact (MK_COMB (@lem2749461 i) (@lem2749460 A m i P)). Qed.
Lemma lem2749463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2749464 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term367 A m i P) = (term368 A m i P).
Proof. exact (MK_COMB (@lem2749463) (@lem2749462 A m i P)). Qed.
Lemma lem2749465 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) (x : A) : (term223 A m i P x) = (term206 A m i P x).
Proof. exact (eq_refl (term223 A m i P x)). Qed.
Lemma lem2749466 (i : int) : (term212 i) = (term212 i).
Proof. exact (eq_refl (term212 i)). Qed.
Lemma lem2749467 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) (x : A) : (term369 A m i P x) = (term370 A m i P x).
Proof. exact (MK_COMB (@lem2749466 i) (@lem2749465 A m i P x)). Qed.
Lemma lem2749468 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term371 A m i P) = (term372 A m i P).
Proof. exact (fun_ext (fun x : A => @lem2749467 A m i P x)). Qed.
Lemma lem2749469 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2749470 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term366 A m i P) = (term373 A m i P).
Proof. exact (MK_COMB (@lem2749469 A) (@lem2749468 A m i P)). Qed.
Lemma lem2749471 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : ((term365 A m i P) = (term366 A m i P)) = ((term362 A m i P) = (term373 A m i P)).
Proof. exact (MK_COMB (@lem2749464 A m i P) (@lem2749470 A m i P)). Qed.
Lemma lem2749472 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term362 A m i P) = (term373 A m i P).
Proof. exact (EQ_MP (@lem2749471 A m i P) (@lem2749456 A m i P)). Qed.
Lemma lem2749473 {A : Type'} (m : A -> int) (P : A -> Prop) : (term363 A m P) = (term374 A m P).
Proof. exact (fun_ext (fun i : int => @lem2749472 A m i P)). Qed.
Lemma lem2749474 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2749475 {A : Type'} (m : A -> int) (P : A -> Prop) : (term364 A m P) = (term375 A m P).
Proof. exact (MK_COMB (@lem2749474) (@lem2749473 A m P)). Qed.
Lemma lem2749488 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) (x : A) : (term370 A m i P x) = (term370 A m i P x).
Proof. exact (eq_refl (term370 A m i P x)). Qed.
Lemma lem2749489 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term372 A m i P) = (term372 A m i P).
Proof. exact (fun_ext (fun x : A => @lem2749488 A m i P x)). Qed.
Lemma lem2749490 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem2749491 {A : Type'} (m : A -> int) (i : int) (P : A -> Prop) : (term373 A m i P) = (term373 A m i P).
Proof. exact (MK_COMB (@lem2749490 A) (@lem2749489 A m i P)). Qed.
Lemma lem2749492 {A : Type'} (m : A -> int) (P : A -> Prop) : (term374 A m P) = (term374 A m P).
Proof. exact (fun_ext (fun i : int => @lem2749491 A m i P)). Qed.
Lemma lem2749493 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2749494 {A : Type'} (m : A -> int) (P : A -> Prop) : (term375 A m P) = (term375 A m P).
Proof. exact (MK_COMB (@lem2749493) (@lem2749492 A m P)). Qed.
Lemma lem2749495 {A : Type'} (m : A -> int) (P : A -> Prop) : (term364 A m P) = (term375 A m P).
Proof. exact (TRANS (@lem2749475 A m P) (@lem2749494 A m P)). Qed.
Lemma lem2749496 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term99 A m P) : term375 A m P.
Proof. exact (EQ_MP (@lem2749495 A m P) (@lem2749408 A m P h1)). Qed.
Lemma lem2749500 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term143 A P x.
Proof. exact (h1). Qed.
Lemma lem2749524 {A : Type'} (_30583 : A) (m : A -> int) (h1 : term23 A m) : term254 A m _30583.
Proof. exact (@lem2749452 A m h1 _30583). Qed.
Lemma lem2749525 {A : Type'} (m : A -> int) (_30583 : A) : (term254 A m _30583) = (term140 A m _30583).
Proof. exact (eq_refl (term254 A m _30583)). Qed.
Lemma lem2749527 {A : Type'} (_30584 : int) (m : A -> int) (P : A -> Prop) (h1 : term99 A m P) : term376 A m P _30584.
Proof. exact (@lem2749496 A m P h1 _30584). Qed.
Lemma lem2749528 {A : Type'} (m : A -> int) (_30584 : int) (P : A -> Prop) : (term376 A m P _30584) = (term373 A m _30584 P).
Proof. exact (eq_refl (term376 A m P _30584)). Qed.
Lemma lem2749529 {A : Type'} (_30584 : int) (m : A -> int) (P : A -> Prop) (h1 : term99 A m P) : term373 A m _30584 P.
Proof. exact (EQ_MP (@lem2749528 A m _30584 P) (@lem2749527 A _30584 m P h1)). Qed.
Lemma lem2749530 {A : Type'} (_30584 : int) (_30585 : A) (m : A -> int) (P : A -> Prop) (h1 : term99 A m P) : term377 A m _30584 P _30585.
Proof. exact (@lem2749529 A _30584 m P h1 _30585). Qed.
Lemma lem2749531 {A : Type'} (m : A -> int) (_30584 : int) (P : A -> Prop) (_30585 : A) : (term377 A m _30584 P _30585) = (term370 A m _30584 P _30585).
Proof. exact (eq_refl (term377 A m _30584 P _30585)). Qed.
Lemma lem2749549 {A : Type'} (_30584 : int) (_30585 : A) (m : A -> int) (P : A -> Prop) (h1 : term99 A m P) : term370 A m _30584 P _30585.
Proof. exact (EQ_MP (@lem2749531 A m _30584 P _30585) (@lem2749530 A _30584 _30585 m P h1)). Qed.
Lemma lem2749551 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term143 A P x.
Proof. exact (h1). Qed.
Lemma lem2749653 {A : Type'} (_30583 : A) (m : A -> int) (h1 : term23 A m) : term140 A m _30583.
Proof. exact (EQ_MP (@lem2749525 A m _30583) (@lem2749524 A _30583 m h1)). Qed.
Lemma lem2749654 {A : Type'} (_30583 : A) (m : A -> int) (h1 : term23 A m) : term140 A m _30583.
Proof. exact (@lem2749653 A _30583 m h1). Qed.
Lemma lem2749655 {A : Type'} (x : A) (m : A -> int) (h1 : term23 A m) : term140 A m x.
Proof. exact (@lem2749654 A x m h1). Qed.
Lemma lem2749656 {A : Type'} (x : A) (m : A -> int) (h1 : term23 A m) : term378 A m x.
Proof. exact (fun h0 : term379 A m x => @lem2749655 A x m h1). Qed.
Lemma lem2749658 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2749659 {A : Type'} (m : A -> int) (x : A) : (term378 A m x) = (term140 A m x).
Proof. exact (@lem2749658 (term140 A m x)). Qed.
Lemma lem2749660 {A : Type'} (x : A) (m : A -> int) (h1 : term23 A m) : term140 A m x.
Proof. exact (EQ_MP (@lem2749659 A m x) (@lem2749656 A x m h1)). Qed.
Lemma lem2749662 (x : int) : x = x.
Proof. exact (@lem21386 int x). Qed.
Lemma lem2749663 {A : Type'} (m : A -> int) (x : A) : (m x) = (m x).
Proof. exact (@lem2749662 (m x)). Qed.
Lemma lem2749664 {A : Type'} (m : A -> int) (x : A) : term380 A m x.
Proof. exact (fun h0 : term381 A m x => @lem2749663 A m x). Qed.
Lemma lem2749666 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2749667 {A : Type'} (m : A -> int) (x : A) : (term380 A m x) = ((m x) = (m x)).
Proof. exact (@lem2749666 ((m x) = (m x))). Qed.
Lemma lem2749668 {A : Type'} (m : A -> int) (x : A) : (m x) = (m x).
Proof. exact (EQ_MP (@lem2749667 A m x) (@lem2749664 A m x)). Qed.
Lemma lem2749674 (q : Prop) (p : Prop) (r : Prop) : (term279 p q r) = (term279 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2749675 {A : Type'} (m : A -> int) (_30584 : int) (P : A -> Prop) (_30585 : A) : (term370 A m _30584 P _30585) = (term382 A m _30584 P _30585).
Proof. exact (@lem2749674 (term282 A m _30585 _30584) (term236 _30584) (P _30585)). Qed.
Lemma lem2749691 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2749692 {A : Type'} (P : A -> Prop) (_30585 : A) (_30584 : int) : (term383 A _30584 P _30585) = (term384 A P _30585 _30584).
Proof. exact (@lem2749691 (P _30585) (term236 _30584)). Qed.
Lemma lem2749698 {A : Type'} (m : A -> int) (_30585 : A) (_30584 : int) : (term286 A m _30585 _30584) = (term286 A m _30585 _30584).
Proof. exact (eq_refl (term286 A m _30585 _30584)). Qed.
Lemma lem2749699 {A : Type'} (m : A -> int) (P : A -> Prop) (_30585 : A) (_30584 : int) : (term382 A m _30584 P _30585) = (term385 A m P _30585 _30584).
Proof. exact (MK_COMB (@lem2749698 A m _30585 _30584) (@lem2749692 A P _30585 _30584)). Qed.
Lemma lem2749703 (q : Prop) (p : Prop) (r : Prop) : (term279 p q r) = (term279 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2749704 {A : Type'} (P : A -> Prop) (m : A -> int) (_30585 : A) (_30584 : int) : (term385 A m P _30585 _30584) = (term386 A P m _30585 _30584).
Proof. exact (@lem2749703 (P _30585) (term282 A m _30585 _30584) (term236 _30584)). Qed.
Lemma lem2749722 {A : Type'} (P : A -> Prop) (m : A -> int) (_30585 : A) (_30584 : int) : (term382 A m _30584 P _30585) = (term386 A P m _30585 _30584).
Proof. exact (TRANS (@lem2749699 A m P _30585 _30584) (@lem2749704 A P m _30585 _30584)). Qed.
Lemma lem2749723 {A : Type'} (P : A -> Prop) (m : A -> int) (_30585 : A) (_30584 : int) : (term370 A m _30584 P _30585) = (term386 A P m _30585 _30584).
Proof. exact (TRANS (@lem2749675 A m _30584 P _30585) (@lem2749722 A P m _30585 _30584)). Qed.
Lemma lem2749724 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2749725 {A : Type'} (P : A -> Prop) (m : A -> int) (_30585 : A) (_30584 : int) : (term387 A m _30584 P _30585) = (term388 A P m _30585 _30584).
Proof. exact (MK_COMB (@lem2749724) (@lem2749723 A P m _30585 _30584)). Qed.
Lemma lem2749739 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2749740 {A : Type'} (m : A -> int) (_30585 : A) (_30584 : int) : (term389 A m _30585 _30584) = (term390 A m _30585 _30584).
Proof. exact (@lem2749739 (term282 A m _30585 _30584) (term236 _30584)). Qed.
Lemma lem2749748 {A : Type'} (P : A -> Prop) (_30585 : A) : (term294 A P _30585) = (term294 A P _30585).
Proof. exact (eq_refl (term294 A P _30585)). Qed.
Lemma lem2749749 {A : Type'} (P : A -> Prop) (m : A -> int) (_30585 : A) (_30584 : int) : (term391 A P m _30585 _30584) = (term386 A P m _30585 _30584).
Proof. exact (MK_COMB (@lem2749748 A P _30585) (@lem2749740 A m _30585 _30584)). Qed.
Lemma lem2749760 {A : Type'} (P : A -> Prop) (m : A -> int) (_30585 : A) (_30584 : int) : ((term370 A m _30584 P _30585) = (term391 A P m _30585 _30584)) = ((term386 A P m _30585 _30584) = (term386 A P m _30585 _30584)).
Proof. exact (MK_COMB (@lem2749725 A P m _30585 _30584) (@lem2749749 A P m _30585 _30584)). Qed.
Lemma lem2749762 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2749763 (x : Prop) : (x = x) = True.
Proof. exact (@lem2749762 Prop x). Qed.
Lemma lem2749764 {A : Type'} (P : A -> Prop) (m : A -> int) (_30585 : A) (_30584 : int) : ((term386 A P m _30585 _30584) = (term386 A P m _30585 _30584)) = True.
Proof. exact (@lem2749763 (term386 A P m _30585 _30584)). Qed.
Lemma lem2749765 {A : Type'} (P : A -> Prop) (m : A -> int) (_30585 : A) (_30584 : int) : ((term370 A m _30584 P _30585) = (term391 A P m _30585 _30584)) = True.
Proof. exact (TRANS (@lem2749760 A P m _30585 _30584) (@lem2749764 A P m _30585 _30584)). Qed.
Lemma lem2749766 {A : Type'} (P : A -> Prop) (m : A -> int) (_30585 : A) (_30584 : int) : True = ((term370 A m _30584 P _30585) = (term391 A P m _30585 _30584)).
Proof. exact (SYM (@lem2749765 A P m _30585 _30584)). Qed.
Lemma lem2749767 {A : Type'} (P : A -> Prop) (m : A -> int) (_30585 : A) (_30584 : int) : (term370 A m _30584 P _30585) = (term391 A P m _30585 _30584).
Proof. exact (EQ_MP (@lem2749766 A P m _30585 _30584) (@lem0)). Qed.
Lemma lem2749768 {A : Type'} (_30585 : A) (_30584 : int) (m : A -> int) (P : A -> Prop) (h1 : term99 A m P) : term391 A P m _30585 _30584.
Proof. exact (EQ_MP (@lem2749767 A P m _30585 _30584) (@lem2749549 A _30584 _30585 m P h1)). Qed.
Lemma lem2749770 (b : Prop) (a : Prop) : (a \/ b) = (term272 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2749771 {A : Type'} (m : A -> int) (_30584 : int) (P : A -> Prop) (_30585 : A) : (term391 A P m _30585 _30584) = (term392 A m _30584 P _30585).
Proof. exact (@lem2749770 (term389 A m _30585 _30584) (P _30585)). Qed.
Lemma lem2749773 (a : Prop) (b : Prop) : (term302 a b) = (term303 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2749774 {A : Type'} (m : A -> int) (_30585 : A) (_30584 : int) : (term393 A m _30585 _30584) = (term394 A m _30585 _30584).
Proof. exact (@lem2749773 (term236 _30584) (term282 A m _30585 _30584)). Qed.
Lemma lem2749776 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2749777 (_30584 : int) : (term306 _30584) = (term215 _30584).
Proof. exact (@lem2749776 (term215 _30584)). Qed.
Lemma lem2749778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2749779 (_30584 : int) : (term307 _30584) = (term308 _30584).
Proof. exact (MK_COMB (@lem2749778) (@lem2749777 _30584)). Qed.
Lemma lem2749781 (a : Prop) : (term112 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2749782 {A : Type'} (m : A -> int) (_30585 : A) (_30584 : int) : (term315 A m _30585 _30584) = ((m _30585) = _30584).
Proof. exact (@lem2749781 ((m _30585) = _30584)). Qed.
Lemma lem2749783 {A : Type'} (m : A -> int) (_30585 : A) (_30584 : int) : (term394 A m _30585 _30584) = (term395 A m _30585 _30584).
Proof. exact (MK_COMB (@lem2749779 _30584) (@lem2749782 A m _30585 _30584)). Qed.
Lemma lem2749784 {A : Type'} (m : A -> int) (_30585 : A) (_30584 : int) : (term393 A m _30585 _30584) = (term395 A m _30585 _30584).
Proof. exact (TRANS (@lem2749774 A m _30585 _30584) (@lem2749783 A m _30585 _30584)). Qed.
Lemma lem2749785 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2749786 {A : Type'} (m : A -> int) (_30585 : A) (_30584 : int) : (term396 A m _30585 _30584) = (term397 A m _30585 _30584).
Proof. exact (MK_COMB (@lem2749785) (@lem2749784 A m _30585 _30584)). Qed.
Lemma lem2749787 {A : Type'} (P : A -> Prop) (_30585 : A) : (P _30585) = (P _30585).
Proof. exact (eq_refl (P _30585)). Qed.
Lemma lem2749788 {A : Type'} (m : A -> int) (_30584 : int) (P : A -> Prop) (_30585 : A) : (term392 A m _30584 P _30585) = (term398 A m _30584 P _30585).
Proof. exact (MK_COMB (@lem2749786 A m _30585 _30584) (@lem2749787 A P _30585)). Qed.
Lemma lem2749789 {A : Type'} (m : A -> int) (_30584 : int) (P : A -> Prop) (_30585 : A) : (term391 A P m _30585 _30584) = (term398 A m _30584 P _30585).
Proof. exact (TRANS (@lem2749771 A m _30584 P _30585) (@lem2749788 A m _30584 P _30585)). Qed.
Lemma lem2749791 {A : Type'} (x : A) (m : A -> int) (h1 : term23 A m) : term399 A m x.
Proof. exact (conj (@lem2749660 A x m h1) (@lem2749668 A m x)). Qed.
Lemma lem2749793 {A : Type'} (_30584 : int) (_30585 : A) (m : A -> int) (P : A -> Prop) (h1 : term99 A m P) : term398 A m _30584 P _30585.
Proof. exact (EQ_MP (@lem2749789 A m _30584 P _30585) (@lem2749768 A _30585 _30584 m P h1)). Qed.
Lemma lem2749794 {A : Type'} (_30584 : int) (_30585 : A) (m : A -> int) (P : A -> Prop) (h1 : term99 A m P) : term398 A m _30584 P _30585.
Proof. exact (@lem2749793 A _30584 _30585 m P h1). Qed.
Lemma lem2749795 {A : Type'} (x : A) (m : A -> int) (P : A -> Prop) (h1 : term99 A m P) : term400 A m P x.
Proof. exact (@lem2749794 A (m x) x m P h1). Qed.
Lemma lem2749798 {A : Type'} (x : A) (m : A -> int) (P : A -> Prop) (h1 : term23 A m) (h2 : term99 A m P) : P x.
Proof. exact (@lem2749795 A x m P h2 (@lem2749791 A x m h1)). Qed.
Lemma lem2749799 {A : Type'} (x : A) (m : A -> int) (P : A -> Prop) (h1 : term23 A m) (h2 : term99 A m P) : P x.
Proof. exact (@lem2749798 A x m P h1 h2). Qed.
Lemma lem2749800 {A : Type'} (x : A) (m : A -> int) (P : A -> Prop) (h1 : term23 A m) (h2 : term99 A m P) : term334 A P x.
Proof. exact (fun h0 : term143 A P x => @lem2749799 A x m P h1 h2). Qed.
Lemma lem2749802 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2749803 {A : Type'} (P : A -> Prop) (x : A) : (term334 A P x) = (P x).
Proof. exact (@lem2749802 (P x)). Qed.
Lemma lem2749804 {A : Type'} (x : A) (m : A -> int) (P : A -> Prop) (h1 : term23 A m) (h2 : term99 A m P) : P x.
Proof. exact (EQ_MP (@lem2749803 A P x) (@lem2749800 A x m P h1 h2)). Qed.
Lemma lem2749807 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2749809 {A : Type'} (P : A -> Prop) (x : A) : (term143 A P x) = (term335 A P x).
Proof. exact (@lem2749807 (P x)). Qed.
Lemma lem2749812 {A : Type'} (P : A -> Prop) (x : A) (h1 : term143 A P x) : term335 A P x.
Proof. exact (EQ_MP (@lem2749809 A P x) (@lem2749551 A P x h1)). Qed.
Lemma lem2749815 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : False.
Proof. exact (@lem2749812 A P x h3 (@lem2749804 A x m P h1 h2)). Qed.
Lemma lem2749816 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : term336.
Proof. exact (fun h0 : ~ False => @lem2749815 A m P x h1 h2 h3). Qed.
Lemma lem2749818 (p : Prop) : (term269 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2749819 : term336 = False.
Proof. exact (@lem2749818 False). Qed.
Lemma lem2749820 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : False.
Proof. exact (EQ_MP (@lem2749819) (@lem2749816 A m P x h1 h2 h3)). Qed.
Lemma lem2749821 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : (term143 A P x) = False.
Proof. exact (prop_ext (fun h4 : term143 A P x => @lem2749820 A m P x h1 h2 h3) (fun h4 : False => @lem2749551 A P x h3)). Qed.
Lemma lem2749822 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : False.
Proof. exact (EQ_MP (@lem2749821 A m P x h1 h2 h3) (@lem2749551 A P x h3)). Qed.
Lemma lem2749823 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : (term143 A P x) = False.
Proof. exact (prop_ext (fun h4 : term143 A P x => @lem2749822 A m P x h1 h2 h3) (fun h4 : False => @lem2749500 A P x h3)). Qed.
Lemma lem2749824 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : False.
Proof. exact (EQ_MP (@lem2749823 A m P x h1 h2 h3) (@lem2749500 A P x h3)). Qed.
Lemma lem2749825 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : (term143 A P x) = False.
Proof. exact (prop_ext (fun h4 : term143 A P x => @lem2749824 A m P x h1 h2 h3) (fun h4 : False => @lem2749500 A P x h3)). Qed.
Lemma lem2749826 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : False.
Proof. exact (EQ_MP (@lem2749825 A m P x h1 h2 h3) (@lem2749500 A P x h3)). Qed.
Lemma lem2749827 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : (term23 A m) = False.
Proof. exact (prop_ext (fun h4 : term23 A m => @lem2749826 A m P x h1 h2 h3) (fun h4 : False => @lem2749452 A m h1)). Qed.
Lemma lem2749828 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : False.
Proof. exact (EQ_MP (@lem2749827 A m P x h1 h2 h3) (@lem2749452 A m h1)). Qed.
Lemma lem2749829 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : (term143 A P x) = False.
Proof. exact (prop_ext (fun h4 : term143 A P x => @lem2749828 A m P x h1 h2 h3) (fun h4 : False => @lem2749414 A P x h3)). Qed.
Lemma lem2749830 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : False.
Proof. exact (EQ_MP (@lem2749829 A m P x h1 h2 h3) (@lem2749414 A P x h3)). Qed.
Lemma lem2749831 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : (term23 A m) = False.
Proof. exact (prop_ext (fun h4 : term23 A m => @lem2749830 A m P x h1 h2 h3) (fun h4 : False => @lem2749372 A m h1)). Qed.
Lemma lem2749832 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term23 A m) (h2 : term99 A m P) (h3 : term143 A P x) : False.
Proof. exact (EQ_MP (@lem2749831 A m P x h1 h2 h3) (@lem2749372 A m h1)). Qed.
Lemma lem2749833 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term99 A m P) (h4 : term143 A P x) : False.
Proof. exact (ex_elim (@lem2749246 A m P h1) (fun y : A -> A => fun h0 : term204 A m P y => @lem2749832 A m P x h2 h3 h4)). Qed.
Lemma lem2749834 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term99 A m P) (h4 : term143 A P x) : (term143 A P x) = False.
Proof. exact (prop_ext (fun h5 : term143 A P x => @lem2749833 A m P x h1 h2 h3 h4) (fun h5 : False => @lem2749356 A P x h4)). Qed.
Lemma lem2749835 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term99 A m P) (h4 : term143 A P x) : False.
Proof. exact (EQ_MP (@lem2749834 A m P x h1 h2 h3 h4) (@lem2749356 A P x h4)). Qed.
Lemma lem2749836 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term99 A m P) (h4 : term143 A P x) : (term23 A m) = False.
Proof. exact (prop_ext (fun h5 : term23 A m => @lem2749835 A m P x h1 h2 h3 h4) (fun h5 : False => @lem2749078 A m h2)). Qed.
Lemma lem2749837 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term99 A m P) (h4 : term143 A P x) : False.
Proof. exact (EQ_MP (@lem2749836 A m P x h1 h2 h3 h4) (@lem2749078 A m h2)). Qed.
Lemma lem2749838 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term99 A m P) (h4 : term143 A P x) : (term143 A P x) = False.
Proof. exact (prop_ext (fun h5 : term143 A P x => @lem2749837 A m P x h1 h2 h3 h4) (fun h5 : False => @lem2749065 A P x h4)). Qed.
Lemma lem2749839 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term99 A m P) (h4 : term143 A P x) : False.
Proof. exact (EQ_MP (@lem2749838 A m P x h1 h2 h3 h4) (@lem2749065 A P x h4)). Qed.
Lemma lem2749840 {A : Type'} (x : A) (m : A -> int) (P : A -> Prop) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term99 A m P) : term142 A P x.
Proof. exact (fun h0 : term143 A P x => @lem2749839 A m P x h1 h2 h3 h0). Qed.
Lemma lem2749841 {A : Type'} (x : A) (m : A -> int) (P : A -> Prop) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term99 A m P) : P x.
Proof. exact (EQ_MP (@lem2749064 A P x) (@lem2749840 A x m P h1 h2 h3)). Qed.
Lemma lem2749842 {A : Type'} (x : A) (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term103 A m P x.
Proof. exact (fun h0 : term99 A m P => @lem2749841 A x m P h1 h2 h0). Qed.
Lemma lem2749843 {A : Type'} (P : A -> Prop) (x : A) (m : A -> int) (h1 : term23 A m) : term347 A m P x.
Proof. exact (fun h0 : term22 A m P => @lem2749842 A x P m h0 h1). Qed.
Lemma lem2749844 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : term348 A m P x.
Proof. exact (fun h0 : term23 A m => @lem2749843 A P x m h0). Qed.
Lemma lem2749849 {A : Type'} (P : A -> Prop) (x : A) : term352 A P x.
Proof. exact (fun m : A -> int => @lem2749844 A m P x). Qed.
Lemma lem2749854 {A : Type'} (x : A) : term356 A x.
Proof. exact (fun P : A -> Prop => @lem2749849 A P x). Qed.
Lemma lem2749859 {A : Type'} : term360 A.
Proof. exact (fun x : A => @lem2749854 A x). Qed.
Lemma lem2749860 {A : Type'} : term359 A.
Proof. exact (EQ_MP (@lem2749057 A) (@lem2749859 A)). Qed.
Lemma lem2749861 {A : Type'} (x : A) : term401 A x.
Proof. exact (@lem2749860 A x). Qed.
Lemma lem2749862 {A : Type'} (x : A) : (term401 A x) = (term355 A x).
Proof. exact (eq_refl (term401 A x)). Qed.
Lemma lem2749863 {A : Type'} (x : A) : term355 A x.
Proof. exact (EQ_MP (@lem2749862 A x) (@lem2749861 A x)). Qed.
Lemma lem2749864 {A : Type'} (x : A) (P : A -> Prop) : term402 A x P.
Proof. exact (@lem2749863 A x P). Qed.
Lemma lem2749865 {A : Type'} (P : A -> Prop) (x : A) : (term402 A x P) = (term351 A P x).
Proof. exact (eq_refl (term402 A x P)). Qed.
Lemma lem2749866 {A : Type'} (P : A -> Prop) (x : A) : term351 A P x.
Proof. exact (EQ_MP (@lem2749865 A P x) (@lem2749864 A x P)). Qed.
Lemma lem2749867 {A : Type'} (P : A -> Prop) (x : A) (m : A -> int) : term403 A P x m.
Proof. exact (@lem2749866 A P x m). Qed.
Lemma lem2749868 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : (term403 A P x m) = (term341 A m P x).
Proof. exact (eq_refl (term403 A P x m)). Qed.
Lemma lem2749869 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : term341 A m P x.
Proof. exact (EQ_MP (@lem2749868 A m P x) (@lem2749867 A P x m)). Qed.
Lemma lem2749871 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) : term341 A m P x.
Proof. exact (@lem2748852 A m P x (@lem2749869 A m P x)). Qed.
Lemma lem2749872 {A : Type'} (P : A -> Prop) (x : A) (m : A -> int) (h1 : term23 A m) : term346 A m P x.
Proof. exact (@lem2749871 A m P x (@lem2747082 A m h1)). Qed.
Lemma lem2749873 {A : Type'} (x : A) (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term339 A m P x.
Proof. exact (@lem2749872 A P x m h2 (@lem2747081 A m P h1)). Qed.
Lemma lem2749874 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term340 A m P x) : False.
Proof. exact (@lem2749873 A x P m h1 h2 (@lem2748836 A m P x h3)). Qed.
Lemma lem2749875 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term340 A m P x) : (term340 A m P x) = False.
Proof. exact (prop_ext (fun h4 : term340 A m P x => @lem2749874 A m P x h1 h2 h3) (fun h4 : False => @lem2748836 A m P x h3)). Qed.
Lemma lem2749876 {A : Type'} (m : A -> int) (P : A -> Prop) (x : A) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term340 A m P x) : False.
Proof. exact (EQ_MP (@lem2749875 A m P x h1 h2 h3) (@lem2748836 A m P x h3)). Qed.
Lemma lem2749877 {A : Type'} (x : A) (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term339 A m P x.
Proof. exact (fun h0 : term340 A m P x => @lem2749876 A m P x h1 h2 h0). Qed.
Lemma lem2749878 {A : Type'} (x : A) (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term103 A m P x.
Proof. exact (EQ_MP (@lem2748835 A m P x) (@lem2749877 A x P m h1 h2)). Qed.
Lemma lem2749879 {A : Type'} (x : A) (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term102 A m P x.
Proof. exact (EQ_MP (@lem2747358 A m P x) (@lem2749878 A x P m h1 h2)). Qed.
Lemma lem2749880 {A : Type'} (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term43 A m P.
Proof. exact (EQ_MP (@lem2747308 A m P) (@lem2748831 A P m h1 h2)). Qed.
Lemma lem2749881 {A : Type'} (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term24 A m P.
Proof. exact (@lem2747107 A m P (@lem2749880 A P m h1 h2)). Qed.
Lemma lem2749882 {A : Type'} (x : A) (m : A -> int) (P : A -> Prop) (h1 : term22 A m P) (h2 : term23 A m) (h3 : term24 A m P) : P x.
Proof. exact (@lem2749879 A x P m h1 h2 (@lem2747083 A m P h3)). Qed.
Lemma lem2749883 {A : Type'} (x : A) (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : (term24 A m P) = (P x).
Proof. exact (prop_ext (fun h3 : term24 A m P => @lem2749882 A x m P h1 h2 h3) (fun h3 : P x => @lem2749881 A P m h1 h2)). Qed.
Lemma lem2749884 {A : Type'} (x : A) (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : P x.
Proof. exact (EQ_MP (@lem2749883 A x P m h1 h2) (@lem2749881 A P m h1 h2)). Qed.
Lemma lem2749889 {A : Type'} (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term404 A P.
Proof. exact (fun x : A => @lem2749884 A x P m h1 h2). Qed.
Lemma lem2749890 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term21 A m P) : term22 A m P.
Proof. exact (proj2 (@lem2747080 A m P h1)). Qed.
Lemma lem2749891 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term21 A m P) : term23 A m.
Proof. exact (proj1 (@lem2747080 A m P h1)). Qed.
Lemma lem2749892 {A : Type'} (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : (term22 A m P) = (term404 A P).
Proof. exact (prop_ext (fun h3 : term22 A m P => @lem2749889 A P m h1 h2) (fun h3 : term404 A P => @lem2747081 A m P h1)). Qed.
Lemma lem2749893 {A : Type'} (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term404 A P.
Proof. exact (EQ_MP (@lem2749892 A P m h1 h2) (@lem2747081 A m P h1)). Qed.
Lemma lem2749894 {A : Type'} (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : (term23 A m) = (term404 A P).
Proof. exact (prop_ext (fun h3 : term23 A m => @lem2749893 A P m h1 h2) (fun h3 : term404 A P => @lem2747082 A m h2)). Qed.
Lemma lem2749895 {A : Type'} (P : A -> Prop) (m : A -> int) (h1 : term22 A m P) (h2 : term23 A m) : term404 A P.
Proof. exact (EQ_MP (@lem2749894 A P m h1 h2) (@lem2747082 A m h2)). Qed.
Lemma lem2749896 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term23 A m) (h2 : term21 A m P) : (term22 A m P) = (term404 A P).
Proof. exact (prop_ext (fun h3 : term22 A m P => @lem2749895 A P m h3 h1) (fun h3 : term404 A P => @lem2749890 A m P h2)). Qed.
Lemma lem2749897 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term23 A m) (h2 : term21 A m P) : term404 A P.
Proof. exact (EQ_MP (@lem2749896 A m P h1 h2) (@lem2749890 A m P h2)). Qed.
Lemma lem2749898 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term21 A m P) : (term23 A m) = (term404 A P).
Proof. exact (prop_ext (fun h2 : term23 A m => @lem2749897 A m P h2 h1) (fun h2 : term404 A P => @lem2749891 A m P h1)). Qed.
Lemma lem2749899 {A : Type'} (m : A -> int) (P : A -> Prop) (h1 : term21 A m P) : term404 A P.
Proof. exact (EQ_MP (@lem2749898 A m P h1) (@lem2749891 A m P h1)). Qed.
Lemma lem2749900 {A : Type'} (m : A -> int) (P : A -> Prop) : term405 A m P.
Proof. exact (fun h0 : term21 A m P => @lem2749899 A m P h0). Qed.
Lemma lem2749905 {A : Type'} (P : A -> Prop) : term406 A P.
Proof. exact (fun m : A -> int => @lem2749900 A m P). Qed.
Lemma lem2749910 {A : Type'} : term407 A.
Proof. exact (fun P : A -> Prop => @lem2749905 A P). Qed.
