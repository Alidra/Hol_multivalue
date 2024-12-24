Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_RESTRICT_SET_term_abbrevs.
Require Import ITERATE_RESTRICT_SET_spec.
Require Import MONOIDAL_ADD_spec.
Require Import NEUTRAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem6990846 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem6990848 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem6990849 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term1 A B op.
Proof. exact (@lem6990848 A B h1 op). Qed.
Lemma lem6990850 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem6990851 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (EQ_MP (@lem6990850 A B op) (@lem6990849 A B op h1)). Qed.
Lemma lem6990852 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem6990853 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem6990851 A B op h1 (@lem6990852 B op h2)). Qed.
Lemma lem6990854 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term4 A B op.
Proof. exact (fun h0 : term0 A B => @lem6990853 A B op h0 h1). Qed.
Lemma lem6990855 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem6990856 {A B : Type'} (op : type1400 B) (h1 : term0 A B) (h2 : @monoidal B op) : term3 A B op.
Proof. exact (@lem6990854 A B op h2 (@lem6990855 A B h1)). Qed.
Lemma lem6990857 {A B : Type'} (op : type1400 B) (h1 : term0 A B) : term2 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem6990856 A B op h1 h0). Qed.
Lemma lem6990858 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun op : type1400 B => @lem6990857 A B op h1). Qed.
Lemma lem6990859 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term0 A B => @lem6990858 A B h0). Qed.
Lemma lem6990860 {A B : Type'} : term0 A B.
Proof. exact (@lem6990859 A B (@lem5986609 A B)). Qed.
Lemma lem6990861 {A B : Type'} (op : type1400 B) : term1 A B op.
Proof. exact (@lem6990860 A B op). Qed.
Lemma lem6990862 {A B : Type'} (op : type1400 B) : (term1 A B op) = (term2 A B op).
Proof. exact (eq_refl (term1 A B op)). Qed.
Lemma lem6990864 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6990865 (h1 : (@neutral nat Nat.add) = (NUMERAL 0)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (SYM (@lem6990864 h1)). Qed.
Lemma lem6990866 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (h1). Qed.
Lemma lem6990867 (h1 : (NUMERAL 0) = (@neutral nat Nat.add)) : (@neutral nat Nat.add) = (NUMERAL 0).
Proof. exact (SYM (@lem6990866 h1)). Qed.
Lemma lem6990868 : ((@neutral nat Nat.add) = (NUMERAL 0)) = ((NUMERAL 0) = (@neutral nat Nat.add)).
Proof. exact (prop_ext (fun h1 : (@neutral nat Nat.add) = (NUMERAL 0) => @lem6990865 h1) (fun h1 : (NUMERAL 0) = (@neutral nat Nat.add) => @lem6990867 h1)). Qed.
Lemma lem6990885 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6990886 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6990885 A). Qed.
Lemma lem6990893 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term6 A s P) = (term6 A s P).
Proof. exact (eq_refl (term6 A s P)). Qed.
Lemma lem6990894 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term7 A s P) = (term8 A s P).
Proof. exact (MK_COMB (@lem6990886 A) (@lem6990893 A s P)). Qed.
Lemma lem6990895 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6990896 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> nat) : (term9 A s P f) = (term10 A s P f).
Proof. exact (MK_COMB (@lem6990894 A s P) (@lem6990895 A f)). Qed.
Lemma lem6990897 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6990898 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> nat) : (term11 A s P f) = (term12 A s P f).
Proof. exact (MK_COMB (@lem6990897) (@lem6990896 A s P f)). Qed.
Lemma lem6990900 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem6990901 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem6990900 A). Qed.
Lemma lem6990902 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem6990903 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem6990901 A) (@lem6990902 A s)). Qed.
Lemma lem6990905 : (NUMERAL 0) = (@neutral nat Nat.add).
Proof. exact (EQ_MP (@lem6990868) (@lem6921993)). Qed.
Lemma lem6990906 {A : Type'} (P : A -> Prop) (f : A -> nat) (x : A) : (term13 A P f x) = (term13 A P f x).
Proof. exact (eq_refl (term13 A P f x)). Qed.
Lemma lem6990907 {A : Type'} (P : A -> Prop) (f : A -> nat) (x : A) : (term14 A P f x) = (term15 A P f x).
Proof. exact (MK_COMB (@lem6990906 A P f x) (@lem6990905)). Qed.
Lemma lem6990908 {A : Type'} (P : A -> Prop) (f : A -> nat) : (term16 A P f) = (term17 A P f).
Proof. exact (fun_ext (fun x : A => @lem6990907 A P f x)). Qed.
Lemma lem6990909 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> nat) : (term18 A s P f) = (term19 A s P f).
Proof. exact (MK_COMB (@lem6990903 A s) (@lem6990908 A P f)). Qed.
Lemma lem6990910 {A : Type'} (s : A -> Prop) (P : A -> Prop) (f : A -> nat) : ((term9 A s P f) = (term18 A s P f)) = ((term10 A s P f) = (term19 A s P f)).
Proof. exact (MK_COMB (@lem6990898 A s P f) (@lem6990909 A s P f)). Qed.
Lemma lem6990913 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term20 A s P) = (term21 A s P).
Proof. exact (fun_ext (fun f : A -> nat => @lem6990910 A s P f)). Qed.
Lemma lem6990914 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6990915 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term22 A s P) = (term23 A s P).
Proof. exact (MK_COMB (@lem6990914 A) (@lem6990913 A s P)). Qed.
Lemma lem6990920 {A : Type'} (P : A -> Prop) : (term24 A P) = (term25 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6990915 A s P)). Qed.
Lemma lem6990921 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6990922 {A : Type'} (P : A -> Prop) : (term26 A P) = (term27 A P).
Proof. exact (MK_COMB (@lem6990921 A) (@lem6990920 A P)). Qed.
Lemma lem6990927 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem6990922 A P)). Qed.
Lemma lem6990928 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6990929 {A : Type'} : (term30 A) = (term31 A).
Proof. exact (MK_COMB (@lem6990928 A) (@lem6990927 A)). Qed.
Lemma lem6990934 {A : Type'} : (term31 A) = (term30 A).
Proof. exact (SYM (@lem6990929 A)). Qed.
Lemma lem6990936 {A B : Type'} (op : type1400 B) : term2 A B op.
Proof. exact (EQ_MP (@lem6990862 A B op) (@lem6990861 A B op)). Qed.
Lemma lem6990937 {A : Type'} (op : type1606) : term32 A op.
Proof. exact (@lem6990936 A nat op). Qed.
Lemma lem6990938 {A : Type'} : term33 A.
Proof. exact (@lem6990937 A Nat.add). Qed.
Lemma lem6990940 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem6990846) (@lem6924403)). Qed.
Lemma lem6990941 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem6990940)). Qed.
Lemma lem6990942 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem6990941) (@lem0)). Qed.
Lemma lem6990943 {A : Type'} : term31 A.
Proof. exact (@lem6990938 A (@lem6990942)). Qed.
Lemma lem6990944 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem6990934 A) (@lem6990943 A)). Qed.
