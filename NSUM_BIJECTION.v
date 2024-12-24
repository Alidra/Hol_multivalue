Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_BIJECTION_term_abbrevs.
Require Import ITERATE_BIJECTION_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem7017844 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem7017846 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7017847 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem7017846 A B h1 op). Qed.
Lemma lem7017848 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7017849 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem7017848 A B op) (@lem7017847 A B op h1)). Qed.
Lemma lem7017850 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem7017851 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7017849 A B op h1 (@lem7017850 B op h2)). Qed.
Lemma lem7017852 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem7017851 A B op h0 h1). Qed.
Lemma lem7017853 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem7017854 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem7017852 A B op h2 (@lem7017853 A B h1)). Qed.
Lemma lem7017855 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem7017854 A B op h1 h0). Qed.
Lemma lem7017856 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem7017855 A B op h1). Qed.
Lemma lem7017857 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem7017856 A B h0). Qed.
Lemma lem7017858 {A B : Type'} : term0 A B.
Proof. exact (@lem7017857 A B (@lem5947359 A B)). Qed.
Lemma lem7017859 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem7017858 A B op). Qed.
Lemma lem7017860 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem7017897 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7017898 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem7017897 A). Qed.
Lemma lem7017899 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7017900 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem7017898 A) (@lem7017899 A s)). Qed.
Lemma lem7017901 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7017902 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@iterate nat A Nat.add s f).
Proof. exact (MK_COMB (@lem7017900 A s) (@lem7017901 A f)). Qed.
Lemma lem7017903 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7017904 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term6 A s f) = (term7 A s f).
Proof. exact (MK_COMB (@lem7017903) (@lem7017902 A s f)). Qed.
Lemma lem7017906 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7017907 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem7017906 A). Qed.
Lemma lem7017908 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7017909 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem7017907 A) (@lem7017908 A s)). Qed.
Lemma lem7017910 {A : Type'} (f : A -> nat) (p : A -> A) : (@o A A nat f p) = (@o A A nat f p).
Proof. exact (eq_refl (@o A A nat f p)). Qed.
Lemma lem7017911 {A : Type'} (s : A -> Prop) (f : A -> nat) (p : A -> A) : (term8 A s f p) = (term9 A s f p).
Proof. exact (MK_COMB (@lem7017909 A s) (@lem7017910 A f p)). Qed.
Lemma lem7017912 {A : Type'} (s : A -> Prop) (f : A -> nat) (p : A -> A) : ((@nsum A s f) = (term8 A s f p)) = ((@iterate nat A Nat.add s f) = (term9 A s f p)).
Proof. exact (MK_COMB (@lem7017904 A s f) (@lem7017911 A s f p)). Qed.
Lemma lem7017915 {A : Type'} (s : A -> Prop) (p : A -> A) : (term10 A s p) = (term10 A s p).
Proof. exact (eq_refl (term10 A s p)). Qed.
Lemma lem7017916 {A : Type'} (s : A -> Prop) (f : A -> nat) (p : A -> A) : (term11 A s f p) = (term12 A s f p).
Proof. exact (MK_COMB (@lem7017915 A s p) (@lem7017912 A s f p)). Qed.
Lemma lem7017919 {A : Type'} (f : A -> nat) (p : A -> A) : (term13 A f p) = (term14 A f p).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7017916 A s f p)). Qed.
Lemma lem7017920 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7017921 {A : Type'} (f : A -> nat) (p : A -> A) : (term15 A f p) = (term16 A f p).
Proof. exact (MK_COMB (@lem7017920 A) (@lem7017919 A f p)). Qed.
Lemma lem7017926 {A : Type'} (f : A -> nat) : (term17 A f) = (term18 A f).
Proof. exact (fun_ext (fun p : A -> A => @lem7017921 A f p)). Qed.
Lemma lem7017927 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem7017928 {A : Type'} (f : A -> nat) : (term19 A f) = (term20 A f).
Proof. exact (MK_COMB (@lem7017927 A) (@lem7017926 A f)). Qed.
Lemma lem7017933 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem7017928 A f)). Qed.
Lemma lem7017934 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7017935 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem7017934 A) (@lem7017933 A)). Qed.
Lemma lem7017940 {A : Type'} : (term24 A) = (term23 A).
Proof. exact (SYM (@lem7017935 A)). Qed.
Lemma lem7017942 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem7017860 A B op) (@lem7017859 A B op)). Qed.
Lemma lem7017943 {A : Type'} (op : type1606) : term25 A op.
Proof. exact (@lem7017942 A nat op). Qed.
Lemma lem7017944 {A : Type'} : term26 A.
Proof. exact (@lem7017943 A Nat.add). Qed.
Lemma lem7017946 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem7017844) (@lem6924403)). Qed.
Lemma lem7017947 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem7017946)). Qed.
Lemma lem7017948 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem7017947) (@lem0)). Qed.
Lemma lem7017949 {A : Type'} : term24 A.
Proof. exact (@lem7017944 A (@lem7017948)). Qed.
Lemma lem7017950 {A : Type'} : term23 A.
Proof. exact (EQ_MP (@lem7017940 A) (@lem7017949 A)). Qed.
