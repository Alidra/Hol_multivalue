Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_BIJECTION_term_abbrevs.
Require Import ITERATE_BIJECTION_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7178039 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7178041 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7178042 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem7178041 A B h1 op). Qed.
Lemma lem7178043 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7178044 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem7178043 A B op) (@lem7178042 A B op h1)). Qed.
Lemma lem7178045 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7178046 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7178044 A B op h1 (@lem7178045 B op h2)). Qed.
Lemma lem7178047 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem7178046 A B op h0 h1). Qed.
Lemma lem7178048 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7178049 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7178047 A B op h2 (@lem7178048 A B h1)). Qed.
Lemma lem7178050 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem7178049 A B op h1 h0). Qed.
Lemma lem7178051 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem7178050 A B op h1). Qed.
Lemma lem7178052 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem7178051 A B h0). Qed.
Lemma lem7178053 {A B : Type'} : term0 A B.
Proof. exact (@lem7178052 A B (@lem5947359 A B)). Qed.
Lemma lem7178054 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem7178053 A B op). Qed.
Lemma lem7178055 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7178092 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178093 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7178092 A). Qed.
Lemma lem7178094 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7178095 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7178093 A) (@lem7178094 A s)). Qed.
Lemma lem7178096 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7178097 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@iterate real A real_add s f).
Proof. exact (MK_COMB (@lem7178095 A s) (@lem7178096 A f)). Qed.
Lemma lem7178098 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7178099 {A : Type'} (s : A -> Prop) (f : A -> real) : (term6 A s f) = (term7 A s f).
Proof. exact (MK_COMB (@lem7178098) (@lem7178097 A s f)). Qed.
Lemma lem7178101 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7178102 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7178101 A). Qed.
Lemma lem7178103 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7178104 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7178102 A) (@lem7178103 A s)). Qed.
Lemma lem7178105 {A : Type'} (f : A -> real) (p : A -> A) : (@o A A real f p) = (@o A A real f p).
Proof. exact (eq_refl (@o A A real f p)). Qed.
Lemma lem7178106 {A : Type'} (s : A -> Prop) (f : A -> real) (p : A -> A) : (term8 A s f p) = (term9 A s f p).
Proof. exact (MK_COMB (@lem7178104 A s) (@lem7178105 A f p)). Qed.
Lemma lem7178107 {A : Type'} (s : A -> Prop) (f : A -> real) (p : A -> A) : ((@sum A s f) = (term8 A s f p)) = ((@iterate real A real_add s f) = (term9 A s f p)).
Proof. exact (MK_COMB (@lem7178099 A s f) (@lem7178106 A s f p)). Qed.
Lemma lem7178110 {A : Type'} (s : A -> Prop) (p : A -> A) : (term10 A s p) = (term10 A s p).
Proof. exact (eq_refl (term10 A s p)). Qed.
Lemma lem7178111 {A : Type'} (s : A -> Prop) (f : A -> real) (p : A -> A) : (term11 A s f p) = (term12 A s f p).
Proof. exact (MK_COMB (@lem7178110 A s p) (@lem7178107 A s f p)). Qed.
Lemma lem7178114 {A : Type'} (f : A -> real) (p : A -> A) : (term13 A f p) = (term14 A f p).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7178111 A s f p)). Qed.
Lemma lem7178115 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7178116 {A : Type'} (f : A -> real) (p : A -> A) : (term15 A f p) = (term16 A f p).
Proof. exact (MK_COMB (@lem7178115 A) (@lem7178114 A f p)). Qed.
Lemma lem7178121 {A : Type'} (f : A -> real) : (term17 A f) = (term18 A f).
Proof. exact (fun_ext (fun p : A -> A => @lem7178116 A f p)). Qed.
Lemma lem7178122 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem7178123 {A : Type'} (f : A -> real) : (term19 A f) = (term20 A f).
Proof. exact (MK_COMB (@lem7178122 A) (@lem7178121 A f)). Qed.
Lemma lem7178128 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7178123 A f)). Qed.
Lemma lem7178129 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7178130 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem7178129 A) (@lem7178128 A)). Qed.
Lemma lem7178135 {A : Type'} : (term24 A) = (term23 A).
Proof. exact (SYM (@lem7178130 A)). Qed.
Lemma lem7178137 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem7178055 A B op) (@lem7178054 A B op)). Qed.
Lemma lem7178138 {A : Type'} (op : type1627) : term25 A op.
Proof. exact (@lem7178137 A real op). Qed.
Lemma lem7178139 {A : Type'} : term26 A.
Proof. exact (@lem7178138 A real_add). Qed.
Lemma lem7178141 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7178039) (@lem7067132)). Qed.
Lemma lem7178142 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7178141)). Qed.
Lemma lem7178143 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7178142) (@lem0)). Qed.
Lemma lem7178144 {A : Type'} : term24 A.
Proof. exact (@lem7178139 A (@lem7178143)). Qed.
Lemma lem7178145 {A : Type'} : term23 A.
Proof. exact (EQ_MP (@lem7178135 A) (@lem7178144 A)). Qed.
