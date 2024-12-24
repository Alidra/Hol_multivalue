Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_UNIV_term_abbrevs.
Require Import ITERATE_UNIV_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Lemma lem7124973 : (@monoidal real real_add) = ((@monoidal real real_add) = True).
Proof. exact (@lem7 (@monoidal real real_add)). Qed.
Lemma lem7124975 {_127673 _127692 : Type'} (h1 : term0 _127673 _127692) : term0 _127673 _127692.
Proof. exact (h1). Qed.
Lemma lem7124976 {_127673 _127692 : Type'} (op : type1400 _127673) (h1 : term0 _127673 _127692) : term1 _127673 _127692 op.
Proof. exact (@lem7124975 _127673 _127692 h1 op). Qed.
Lemma lem7124977 {_127673 _127692 : Type'} (op : type1400 _127673) : (term1 _127673 _127692 op) = (term2 _127673 _127692 op).
Proof. exact (eq_refl (term1 _127673 _127692 op)). Qed.
Lemma lem7124978 {_127673 _127692 : Type'} (op : type1400 _127673) (h1 : term0 _127673 _127692) : term2 _127673 _127692 op.
Proof. exact (EQ_MP (@lem7124977 _127673 _127692 op) (@lem7124976 _127673 _127692 op h1)). Qed.
Lemma lem7124979 {_127673 : Type'} (op : type1400 _127673) (h1 : @monoidal _127673 op) : @monoidal _127673 op.
Proof. exact (h1). Qed.
Lemma lem7124980 {_127673 _127692 : Type'} (op : type1400 _127673) (h1 : term0 _127673 _127692) (h2 : @monoidal _127673 op) : term3 _127673 _127692 op.
Proof. exact (@lem7124978 _127673 _127692 op h1 (@lem7124979 _127673 op h2)). Qed.
Lemma lem7124981 {_127673 _127692 : Type'} (op : type1400 _127673) (h1 : @monoidal _127673 op) : term4 _127673 _127692 op.
Proof. exact (fun h0 : term0 _127673 _127692 => @lem7124980 _127673 _127692 op h0 h1). Qed.
Lemma lem7124982 {_127673 _127692 : Type'} (h1 : term0 _127673 _127692) : term0 _127673 _127692.
Proof. exact (h1). Qed.
Lemma lem7124983 {_127673 _127692 : Type'} (op : type1400 _127673) (h1 : term0 _127673 _127692) (h2 : @monoidal _127673 op) : term3 _127673 _127692 op.
Proof. exact (@lem7124981 _127673 _127692 op h2 (@lem7124982 _127673 _127692 h1)). Qed.
Lemma lem7124984 {_127673 _127692 : Type'} (op : type1400 _127673) (h1 : term0 _127673 _127692) : term2 _127673 _127692 op.
Proof. exact (fun h0 : @monoidal _127673 op => @lem7124983 _127673 _127692 op h1 h0). Qed.
Lemma lem7124985 {_127673 _127692 : Type'} (h1 : term0 _127673 _127692) : term0 _127673 _127692.
Proof. exact (fun op : type1400 _127673 => @lem7124984 _127673 _127692 op h1). Qed.
Lemma lem7124986 {_127673 _127692 : Type'} : term5 _127673 _127692.
Proof. exact (fun h0 : term0 _127673 _127692 => @lem7124985 _127673 _127692 h0). Qed.
Lemma lem7124987 {_127673 _127692 : Type'} : term0 _127673 _127692.
Proof. exact (@lem7124986 _127673 _127692 (@lem6963073 _127673 _127692)). Qed.
Lemma lem7124988 {_127673 _127692 : Type'} (op : type1400 _127673) : term1 _127673 _127692 op.
Proof. exact (@lem7124987 _127673 _127692 op). Qed.
Lemma lem7124989 {_127673 _127692 : Type'} (op : type1400 _127673) : (term1 _127673 _127692 op) = (term2 _127673 _127692 op).
Proof. exact (eq_refl (term1 _127673 _127692 op)). Qed.
Lemma lem7125004 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7125005 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7125004 A). Qed.
Lemma lem7125006 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7125007 {A : Type'} (s : A -> Prop) : (@sum A s) = (@iterate real A real_add s).
Proof. exact (MK_COMB (@lem7125005 A) (@lem7125006 A s)). Qed.
Lemma lem7125008 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7125009 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (@iterate real A real_add s f).
Proof. exact (MK_COMB (@lem7125007 A s) (@lem7125008 A f)). Qed.
Lemma lem7125010 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7125011 {A : Type'} (s : A -> Prop) (f : A -> real) : (term6 A s f) = (term7 A s f).
Proof. exact (MK_COMB (@lem7125010) (@lem7125009 A s f)). Qed.
Lemma lem7125013 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7125014 {A : Type'} : (@sum A) = (@iterate real A real_add).
Proof. exact (@lem7125013 A). Qed.
Lemma lem7125015 {A : Type'} : (@UNIV A) = (@UNIV A).
Proof. exact (eq_refl (@UNIV A)). Qed.
Lemma lem7125016 {A : Type'} : (@sum A (@UNIV A)) = (@iterate real A real_add (@UNIV A)).
Proof. exact (MK_COMB (@lem7125014 A) (@lem7125015 A)). Qed.
Lemma lem7125017 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7125018 {A : Type'} (f : A -> real) : (@sum A (@UNIV A) f) = (@iterate real A real_add (@UNIV A) f).
Proof. exact (MK_COMB (@lem7125016 A) (@lem7125017 A f)). Qed.
Lemma lem7125019 {A : Type'} (s : A -> Prop) (f : A -> real) : ((@sum A s f) = (@sum A (@UNIV A) f)) = ((@iterate real A real_add s f) = (@iterate real A real_add (@UNIV A) f)).
Proof. exact (MK_COMB (@lem7125011 A s f) (@lem7125018 A f)). Qed.
Lemma lem7125022 {A : Type'} (f : A -> real) (s : A -> Prop) : (term8 A f s) = (term8 A f s).
Proof. exact (eq_refl (term8 A f s)). Qed.
Lemma lem7125023 {A : Type'} (s : A -> Prop) (f : A -> real) : (term9 A s f) = (term10 A s f).
Proof. exact (MK_COMB (@lem7125022 A f s) (@lem7125019 A s f)). Qed.
Lemma lem7125026 {A : Type'} (f : A -> real) : (term11 A f) = (term12 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7125023 A s f)). Qed.
Lemma lem7125027 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7125028 {A : Type'} (f : A -> real) : (term13 A f) = (term14 A f).
Proof. exact (MK_COMB (@lem7125027 A) (@lem7125026 A f)). Qed.
Lemma lem7125033 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7125028 A f)). Qed.
Lemma lem7125034 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7125035 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (MK_COMB (@lem7125034 A) (@lem7125033 A)). Qed.
Lemma lem7125040 {A : Type'} : (term18 A) = (term17 A).
Proof. exact (SYM (@lem7125035 A)). Qed.
Lemma lem7125042 {_127673 _127692 : Type'} (op : type1400 _127673) : term2 _127673 _127692 op.
Proof. exact (EQ_MP (@lem7124989 _127673 _127692 op) (@lem7124988 _127673 _127692 op)). Qed.
Lemma lem7125043 {A : Type'} (op : type1627) : term19 A op.
Proof. exact (@lem7125042 real A op). Qed.
Lemma lem7125044 {A : Type'} : term20 A.
Proof. exact (@lem7125043 A real_add). Qed.
Lemma lem7125046 : (@monoidal real real_add) = True.
Proof. exact (EQ_MP (@lem7124973) (@lem7067132)). Qed.
Lemma lem7125047 : True = (@monoidal real real_add).
Proof. exact (SYM (@lem7125046)). Qed.
Lemma lem7125048 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7125047) (@lem0)). Qed.
Lemma lem7125049 {A : Type'} : term18 A.
Proof. exact (@lem7125044 A (@lem7125048)). Qed.
Lemma lem7125050 {A : Type'} : term17 A.
Proof. exact (EQ_MP (@lem7125040 A) (@lem7125049 A)). Qed.
