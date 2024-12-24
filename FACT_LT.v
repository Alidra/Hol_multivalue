Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FACT_LT_term_abbrevs.
Require Import LT_0_spec.
Require Import LT_MULT_spec.
Require Import thm0_spec.
Require Import thm146107_spec.
Require Import thm1843_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm80360_spec.
Lemma lem146111 (n : nat) : term0 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem146112 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem146113 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem146112 n) (@lem146111 n)). Qed.
Lemma lem146114 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem146117 (P : nat -> Prop) : term2 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem146118 : term3.
Proof. exact (@lem146117 term4). Qed.
Lemma lem146119 : term5 = term6.
Proof. exact (eq_refl term5). Qed.
Lemma lem146120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem146121 : term7 = term8.
Proof. exact (MK_COMB (@lem146120) (@lem146119)). Qed.
Lemma lem146122 (n : nat) : (term9 n) = (term10 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem146123 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem146124 (n : nat) : (term11 n) = (term12 n).
Proof. exact (MK_COMB (@lem146123) (@lem146122 n)). Qed.
Lemma lem146125 (n : nat) : (term13 n) = (term14 n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem146126 (n : nat) : (term15 n) = (term16 n).
Proof. exact (MK_COMB (@lem146124 n) (@lem146125 n)). Qed.
Lemma lem146127 : term17 = term18.
Proof. exact (fun_ext (fun n : nat => @lem146126 n)). Qed.
Lemma lem146128 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem146129 : term19 = term20.
Proof. exact (MK_COMB (@lem146128) (@lem146127)). Qed.
Lemma lem146130 : term21 = term22.
Proof. exact (MK_COMB (@lem146121) (@lem146129)). Qed.
Lemma lem146131 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem146132 : term23 = term24.
Proof. exact (MK_COMB (@lem146131) (@lem146130)). Qed.
Lemma lem146133 (n : nat) : (term9 n) = (term10 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem146134 : term25 = term4.
Proof. exact (fun_ext (fun n : nat => @lem146133 n)). Qed.
Lemma lem146135 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem146136 : term26 = term27.
Proof. exact (MK_COMB (@lem146135) (@lem146134)). Qed.
Lemma lem146137 : term3 = term28.
Proof. exact (MK_COMB (@lem146132) (@lem146136)). Qed.
Lemma lem146138 : term28.
Proof. exact (EQ_MP (@lem146137) (@lem146118)). Qed.
Lemma lem146139 (n : nat) (h1 : term10 n) : term10 n.
Proof. exact (h1). Qed.
Lemma lem146152 : term29 = term30.
Proof. exact (proj1 (@lem146107)). Qed.
Lemma lem146153 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem146154 : term6 = term32.
Proof. exact (MK_COMB (@lem146153) (@lem146152)). Qed.
Lemma lem146155 : term32 = term6.
Proof. exact (SYM (@lem146154)). Qed.
Lemma lem146156 (m : nat) : term33 m.
Proof. exact (@lem102215 m). Qed.
Lemma lem146157 (m : nat) : (term33 m) = (term34 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem146158 (m : nat) : term34 m.
Proof. exact (EQ_MP (@lem146157 m) (@lem146156 m)). Qed.
Lemma lem146159 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem146158 m n). Qed.
Lemma lem146160 (m : nat) (n : nat) : (term35 m n) = ((term36 m n) = (term37 m n)).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem146162 : term38.
Proof. exact (proj2 (@lem146107)). Qed.
Lemma lem146163 (n : nat) : term39 n.
Proof. exact (@lem146162 n). Qed.
Lemma lem146164 (n : nat) : (term39 n) = ((term40 n) = (term41 n)).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem146167 (n : nat) : (term10 n) = ((term10 n) = True).
Proof. exact (@lem7 (term10 n)). Qed.
Lemma lem146170 (n : nat) : (term40 n) = (term41 n).
Proof. exact (EQ_MP (@lem146164 n) (@lem146163 n)). Qed.
Lemma lem146171 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem146172 (n : nat) : (term14 n) = (term42 n).
Proof. exact (MK_COMB (@lem146171) (@lem146170 n)). Qed.
Lemma lem146174 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (EQ_MP (@lem146160 m n) (@lem146159 m n)). Qed.
Lemma lem146175 (n : nat) : (term42 n) = (term43 n).
Proof. exact (@lem146174 (S n) (Factorial.fact n)). Qed.
Lemma lem146179 (n : nat) (h1 : term10 n) : (term10 n) = True.
Proof. exact (EQ_MP (@lem146167 n) (@lem146139 n h1)). Qed.
Lemma lem146180 (n : nat) : (term44 n) = (term44 n).
Proof. exact (eq_refl (term44 n)). Qed.
Lemma lem146181 (n : nat) (h1 : term10 n) : (term43 n) = (term45 n).
Proof. exact (MK_COMB (@lem146180 n) (@lem146179 n h1)). Qed.
Lemma lem146183 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem146184 (n : nat) : (term45 n) = (term1 n).
Proof. exact (@lem146183 (term1 n)). Qed.
Lemma lem146185 (n : nat) (h1 : term10 n) : (term43 n) = (term1 n).
Proof. exact (TRANS (@lem146181 n h1) (@lem146184 n)). Qed.
Lemma lem146186 (n : nat) (h1 : term10 n) : (term42 n) = (term1 n).
Proof. exact (TRANS (@lem146175 n) (@lem146185 n h1)). Qed.
Lemma lem146187 (n : nat) (h1 : term10 n) : (term14 n) = (term1 n).
Proof. exact (TRANS (@lem146172 n) (@lem146186 n h1)). Qed.
Lemma lem146188 (n : nat) (h1 : term10 n) : (term1 n) = (term14 n).
Proof. exact (SYM (@lem146187 n h1)). Qed.
Lemma lem146190 : term30 = term46.
Proof. exact (EQ_MP (@lem80360) (@lem0)). Qed.
Lemma lem146191 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem146192 : term32 = term47.
Proof. exact (MK_COMB (@lem146191) (@lem146190)). Qed.
Lemma lem146194 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem146114 n) (@lem146113 n)). Qed.
Lemma lem146195 : term47 = True.
Proof. exact (@lem146194 (NUMERAL 0)). Qed.
Lemma lem146196 : term32 = True.
Proof. exact (TRANS (@lem146192) (@lem146195)). Qed.
Lemma lem146197 : True = term32.
Proof. exact (SYM (@lem146196)). Qed.
Lemma lem146198 : term32.
Proof. exact (EQ_MP (@lem146197) (@lem0)). Qed.
Lemma lem146200 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem146114 n) (@lem146113 n)). Qed.
Lemma lem146201 (n : nat) : True = (term1 n).
Proof. exact (SYM (@lem146200 n)). Qed.
Lemma lem146202 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem146201 n) (@lem0)). Qed.
Lemma lem146203 (n : nat) (h1 : term10 n) : term14 n.
Proof. exact (EQ_MP (@lem146188 n h1) (@lem146202 n)). Qed.
Lemma lem146204 : term6.
Proof. exact (EQ_MP (@lem146155) (@lem146198)). Qed.
Lemma lem146205 (n : nat) : term16 n.
Proof. exact (fun h0 : term10 n => @lem146203 n h0). Qed.
Lemma lem146210 : term20.
Proof. exact (fun n : nat => @lem146205 n). Qed.
Lemma lem146211 : term22.
Proof. exact (conj (@lem146204) (@lem146210)). Qed.
Lemma lem146212 : term27.
Proof. exact (@lem146138 (@lem146211)). Qed.
