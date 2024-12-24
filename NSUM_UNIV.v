Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_UNIV_term_abbrevs.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6017756_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem6962132 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6962134 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem6962135 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem6962134 A B h1 op). Qed.
Lemma lem6962136 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem6962137 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem6962136 A B op) (@lem6962135 A B op h1)). Qed.
Lemma lem6962138 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6962139 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem6962137 A B op h1 (@lem6962138 B op h2)). Qed.
Lemma lem6962140 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem6962139 A B op h0 h1). Qed.
Lemma lem6962141 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem6962142 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem6962140 A B op h2 (@lem6962141 A B h1)). Qed.
Lemma lem6962143 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem6962142 A B op h1 h0). Qed.
Lemma lem6962144 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem6962143 A B op h1). Qed.
Lemma lem6962145 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem6962144 A B h0). Qed.
Lemma lem6962146 {A B : Type'} : term0 A B.
Proof. exact (@lem6962145 A B (@lem6017756 A B)). Qed.
Lemma lem6962147 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem6962146 A B op). Qed.
Lemma lem6962148 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem6962163 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6962164 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6962163 A). Qed.
Lemma lem6962165 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6962166 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem6962164 A) (@lem6962165 A s)). Qed.
Lemma lem6962167 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6962168 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@iterate nat A Nat.add s f).
Proof. exact (MK_COMB (@lem6962166 A s) (@lem6962167 A f)). Qed.
Lemma lem6962169 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6962170 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term6 A s f) = (term7 A s f).
Proof. exact (MK_COMB (@lem6962169) (@lem6962168 A s f)). Qed.
Lemma lem6962172 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6962173 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6962172 A). Qed.
Lemma lem6962174 {A : Type'} : (@UNIV A) = (@UNIV A).
Proof. exact (eq_refl (@UNIV A)). Qed.
Lemma lem6962175 {A : Type'} : (@nsum A (@UNIV A)) = (@iterate nat A Nat.add (@UNIV A)).
Proof. exact (MK_COMB (@lem6962173 A) (@lem6962174 A)). Qed.
Lemma lem6962176 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6962177 {A : Type'} (f : A -> nat) : (@nsum A (@UNIV A) f) = (@iterate nat A Nat.add (@UNIV A) f).
Proof. exact (MK_COMB (@lem6962175 A) (@lem6962176 A f)). Qed.
Lemma lem6962178 {A : Type'} (s : A -> Prop) (f : A -> nat) : ((@nsum A s f) = (@nsum A (@UNIV A) f)) = ((@iterate nat A Nat.add s f) = (@iterate nat A Nat.add (@UNIV A) f)).
Proof. exact (MK_COMB (@lem6962170 A s f) (@lem6962177 A f)). Qed.
Lemma lem6962181 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term8 A f s) = (term8 A f s).
Proof. exact (eq_refl (term8 A f s)). Qed.
Lemma lem6962182 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term9 A s f) = (term10 A s f).
Proof. exact (MK_COMB (@lem6962181 A f s) (@lem6962178 A s f)). Qed.
Lemma lem6962185 {A : Type'} (f : A -> nat) : (term11 A f) = (term12 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6962182 A s f)). Qed.
Lemma lem6962186 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6962187 {A : Type'} (f : A -> nat) : (term13 A f) = (term14 A f).
Proof. exact (MK_COMB (@lem6962186 A) (@lem6962185 A f)). Qed.
Lemma lem6962192 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6962187 A f)). Qed.
Lemma lem6962193 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6962194 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (MK_COMB (@lem6962193 A) (@lem6962192 A)). Qed.
Lemma lem6962199 {A : Type'} : (term18 A) = (term17 A).
Proof. exact (SYM (@lem6962194 A)). Qed.
Lemma lem6962201 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem6962148 A B op) (@lem6962147 A B op)). Qed.
Lemma lem6962202 {A : Type'} (op : type1606) : term19 A op.
Proof. exact (@lem6962201 A nat op). Qed.
Lemma lem6962203 {A : Type'} : term20 A.
Proof. exact (@lem6962202 A Nat.add). Qed.
Lemma lem6962205 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6962132) (@lem6924403)). Qed.
Lemma lem6962206 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem6962205)). Qed.
Lemma lem6962207 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem6962206) (@lem0)). Qed.
Lemma lem6962208 {A : Type'} : term18 A.
Proof. exact (@lem6962203 A (@lem6962207)). Qed.
Lemma lem6962209 {A : Type'} : term17 A.
Proof. exact (EQ_MP (@lem6962199 A) (@lem6962208 A)). Qed.
