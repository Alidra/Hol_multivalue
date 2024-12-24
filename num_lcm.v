Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import num_lcm_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem2840120 : num_lcm = term0.
Proof. exact (@num_lcm_def). Qed.
Lemma lem2840121 (_31190 : prod nat nat) : _31190 = _31190.
Proof. exact (eq_refl _31190). Qed.
Lemma lem2840122 (_31190 : prod nat nat) : (num_lcm _31190) = (term1 _31190).
Proof. exact (MK_COMB (@lem2840120) (@lem2840121 _31190)). Qed.
Lemma lem2840123 (_31190 : prod nat nat) : (term1 _31190) = (term2 _31190).
Proof. exact (eq_refl (term1 _31190)). Qed.
Lemma lem2840124 (_31190 : prod nat nat) : (num_lcm _31190) = (term2 _31190).
Proof. exact (TRANS (@lem2840122 _31190) (@lem2840123 _31190)). Qed.
Lemma lem2840125 : term3.
Proof. exact (fun _31190 : prod nat nat => @lem2840124 _31190). Qed.
Lemma lem2840126 (_31190 : prod nat nat) : term4 _31190.
Proof. exact (@lem2840125 _31190). Qed.
Lemma lem2840127 (_31190 : prod nat nat) : (term4 _31190) = ((num_lcm _31190) = (term2 _31190)).
Proof. exact (eq_refl (term4 _31190)). Qed.
Lemma lem2840128 (_31190 : prod nat nat) : (num_lcm _31190) = (term2 _31190).
Proof. exact (EQ_MP (@lem2840127 _31190) (@lem2840126 _31190)). Qed.
Lemma lem2840129 (a : nat) (b : nat) : (term5 a b) = (term6 a b).
Proof. exact (@lem2840128 (@pair nat nat a b)). Qed.
Lemma lem2840130 {A B : Type'} (x : A) : term7 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem2840131 {A B : Type'} (x : A) : (term7 A B x) = (term8 A B x).
Proof. exact (eq_refl (term7 A B x)). Qed.
Lemma lem2840132 {A B : Type'} (x : A) : term8 A B x.
Proof. exact (EQ_MP (@lem2840131 A B x) (@lem2840130 A B x)). Qed.
Lemma lem2840133 {A B : Type'} (x : A) (y : B) : term9 A B x y.
Proof. exact (@lem2840132 A B x y). Qed.
Lemma lem2840134 {A B : Type'} (x : A) (y : B) : (term9 A B x y) = ((term10 A B x y) = y).
Proof. exact (eq_refl (term9 A B x y)). Qed.
Lemma lem2840136 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem2840137 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem2840138 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem2840137 A B x) (@lem2840136 A B x)). Qed.
Lemma lem2840139 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem2840138 A B x y). Qed.
Lemma lem2840140 {A B : Type'} (y : B) (x : A) : (term13 A B x y) = ((term14 A B x y) = x).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem2840143 {A B : Type'} (y : B) (x : A) : (term14 A B x y) = x.
Proof. exact (EQ_MP (@lem2840140 A B y x) (@lem2840139 A B x y)). Qed.
Lemma lem2840144 (y : nat) (x : nat) : (term15 x y) = x.
Proof. exact (@lem2840143 nat nat y x). Qed.
Lemma lem2840145 (b : nat) (a : nat) : (term15 a b) = a.
Proof. exact (@lem2840144 b a). Qed.
Lemma lem2840146 (a : nat) (b : nat) : a = (term15 a b).
Proof. exact (SYM (@lem2840145 b a)). Qed.
Lemma lem2840148 {A B : Type'} (x : A) (y : B) : (term10 A B x y) = y.
Proof. exact (EQ_MP (@lem2840134 A B x y) (@lem2840133 A B x y)). Qed.
Lemma lem2840149 (x : nat) (y : nat) : (term16 x y) = y.
Proof. exact (@lem2840148 nat nat x y). Qed.
Lemma lem2840150 (a : nat) (b : nat) : (term16 a b) = b.
Proof. exact (@lem2840149 a b). Qed.
Lemma lem2840151 (a : nat) (b : nat) : b = (term16 a b).
Proof. exact (SYM (@lem2840150 a b)). Qed.
Lemma lem2840152 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem2840153 (a : nat) (b : nat) : (term18 a) = (term19 a b).
Proof. exact (MK_COMB (@lem2840152) (@lem2840146 a b)). Qed.
Lemma lem2840154 (a : nat) (b : nat) : (term19 a b) = (term20 a b).
Proof. exact (eq_refl (term19 a b)). Qed.
Lemma lem2840155 (a : nat) : (term21 a) = (term21 a).
Proof. exact (eq_refl (term21 a)). Qed.
Lemma lem2840156 (a : nat) (b : nat) : ((term18 a) = (term19 a b)) = ((term18 a) = (term20 a b)).
Proof. exact (MK_COMB (@lem2840155 a) (@lem2840154 a b)). Qed.
Lemma lem2840157 (a : nat) : (term18 a) = (term22 a).
Proof. exact (eq_refl (term18 a)). Qed.
Lemma lem2840158 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem2840159 (a : nat) : (term21 a) = (term23 a).
Proof. exact (MK_COMB (@lem2840158) (@lem2840157 a)). Qed.
Lemma lem2840160 (a : nat) (b : nat) : (term20 a b) = (term20 a b).
Proof. exact (eq_refl (term20 a b)). Qed.
Lemma lem2840161 (a : nat) (b : nat) : ((term18 a) = (term20 a b)) = ((term22 a) = (term20 a b)).
Proof. exact (MK_COMB (@lem2840159 a) (@lem2840160 a b)). Qed.
Lemma lem2840162 (a : nat) (b : nat) : ((term18 a) = (term19 a b)) = ((term22 a) = (term20 a b)).
Proof. exact (TRANS (@lem2840156 a b) (@lem2840161 a b)). Qed.
Lemma lem2840163 (a : nat) (b : nat) : (term22 a) = (term20 a b).
Proof. exact (EQ_MP (@lem2840162 a b) (@lem2840153 a b)). Qed.
Lemma lem2840164 (a : nat) (b : nat) : (term24 a b) = (term25 a b).
Proof. exact (MK_COMB (@lem2840163 a b) (@lem2840151 a b)). Qed.
Lemma lem2840165 (a : nat) (b : nat) : (term25 a b) = (term6 a b).
Proof. exact (eq_refl (term25 a b)). Qed.
Lemma lem2840166 (a : nat) (b : nat) : (term26 a b) = (term26 a b).
Proof. exact (eq_refl (term26 a b)). Qed.
Lemma lem2840167 (a : nat) (b : nat) : ((term24 a b) = (term25 a b)) = ((term24 a b) = (term6 a b)).
Proof. exact (MK_COMB (@lem2840166 a b) (@lem2840165 a b)). Qed.
Lemma lem2840168 (a : nat) (b : nat) : (term24 a b) = (term27 a b).
Proof. exact (eq_refl (term24 a b)). Qed.
Lemma lem2840169 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem2840170 (a : nat) (b : nat) : (term26 a b) = (term28 a b).
Proof. exact (MK_COMB (@lem2840169) (@lem2840168 a b)). Qed.
Lemma lem2840171 (a : nat) (b : nat) : (term6 a b) = (term6 a b).
Proof. exact (eq_refl (term6 a b)). Qed.
Lemma lem2840172 (a : nat) (b : nat) : ((term24 a b) = (term6 a b)) = ((term27 a b) = (term6 a b)).
Proof. exact (MK_COMB (@lem2840170 a b) (@lem2840171 a b)). Qed.
Lemma lem2840173 (a : nat) (b : nat) : ((term24 a b) = (term25 a b)) = ((term27 a b) = (term6 a b)).
Proof. exact (TRANS (@lem2840167 a b) (@lem2840172 a b)). Qed.
Lemma lem2840174 (a : nat) (b : nat) : (term27 a b) = (term6 a b).
Proof. exact (EQ_MP (@lem2840173 a b) (@lem2840164 a b)). Qed.
Lemma lem2840175 (a : nat) (b : nat) : (term6 a b) = (term27 a b).
Proof. exact (SYM (@lem2840174 a b)). Qed.
Lemma lem2840176 (a : nat) (b : nat) : (term5 a b) = (term27 a b).
Proof. exact (TRANS (@lem2840129 a b) (@lem2840175 a b)). Qed.
Lemma lem2840177 (a : nat) : term29 a.
Proof. exact (fun b : nat => @lem2840176 a b). Qed.
Lemma lem2840178 : term30.
Proof. exact (fun a : nat => @lem2840177 a). Qed.
