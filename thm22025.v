Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm22025_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1833_spec.
Lemma lem21939 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem21940 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem21941 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem21940 a) (@lem21939 a)). Qed.
Lemma lem21942 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem21943 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem21952 (c : Prop) : (term2 c) = (term2 c).
Proof. exact (eq_refl (term2 c)). Qed.
Lemma lem21953 (c : Prop) (a : Prop) (h1 : a = True) : (term3 c a) = (term4 c).
Proof. exact (MK_COMB (@lem21952 c) (@lem21942 a h1)). Qed.
Lemma lem21954 (c : Prop) : (term4 c) = (term5 c).
Proof. exact (eq_refl (term4 c)). Qed.
Lemma lem21955 (c : Prop) (a : Prop) : (term6 c a) = (term6 c a).
Proof. exact (eq_refl (term6 c a)). Qed.
Lemma lem21956 (a : Prop) (c : Prop) : ((term3 c a) = (term4 c)) = ((term3 c a) = (term5 c)).
Proof. exact (MK_COMB (@lem21955 c a) (@lem21954 c)). Qed.
Lemma lem21957 (a : Prop) (c : Prop) : (term3 c a) = (term7 a c).
Proof. exact (eq_refl (term3 c a)). Qed.
Lemma lem21958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21959 (a : Prop) (c : Prop) : (term6 c a) = (term8 a c).
Proof. exact (MK_COMB (@lem21958) (@lem21957 a c)). Qed.
Lemma lem21960 (c : Prop) : (term5 c) = (term5 c).
Proof. exact (eq_refl (term5 c)). Qed.
Lemma lem21961 (a : Prop) (c : Prop) : ((term3 c a) = (term5 c)) = ((term7 a c) = (term5 c)).
Proof. exact (MK_COMB (@lem21959 a c) (@lem21960 c)). Qed.
Lemma lem21962 (a : Prop) (c : Prop) : ((term3 c a) = (term4 c)) = ((term7 a c) = (term5 c)).
Proof. exact (TRANS (@lem21956 a c) (@lem21961 a c)). Qed.
Lemma lem21963 (c : Prop) (a : Prop) (h1 : a = True) : (term7 a c) = (term5 c).
Proof. exact (EQ_MP (@lem21962 a c) (@lem21953 c a h1)). Qed.
Lemma lem21964 (c : Prop) (a : Prop) (h1 : a = True) : (term5 c) = (term7 a c).
Proof. exact (SYM (@lem21963 c a h1)). Qed.
Lemma lem21965 (c : Prop) : (term2 c) = (term2 c).
Proof. exact (eq_refl (term2 c)). Qed.
Lemma lem21966 (c : Prop) (a : Prop) (h1 : a = False) : (term3 c a) = (term9 c).
Proof. exact (MK_COMB (@lem21965 c) (@lem21943 a h1)). Qed.
Lemma lem21967 (c : Prop) : (term9 c) = (term10 c).
Proof. exact (eq_refl (term9 c)). Qed.
Lemma lem21968 (c : Prop) (a : Prop) : (term6 c a) = (term6 c a).
Proof. exact (eq_refl (term6 c a)). Qed.
Lemma lem21969 (a : Prop) (c : Prop) : ((term3 c a) = (term9 c)) = ((term3 c a) = (term10 c)).
Proof. exact (MK_COMB (@lem21968 c a) (@lem21967 c)). Qed.
Lemma lem21970 (a : Prop) (c : Prop) : (term3 c a) = (term7 a c).
Proof. exact (eq_refl (term3 c a)). Qed.
Lemma lem21971 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21972 (a : Prop) (c : Prop) : (term6 c a) = (term8 a c).
Proof. exact (MK_COMB (@lem21971) (@lem21970 a c)). Qed.
Lemma lem21973 (c : Prop) : (term10 c) = (term10 c).
Proof. exact (eq_refl (term10 c)). Qed.
Lemma lem21974 (a : Prop) (c : Prop) : ((term3 c a) = (term10 c)) = ((term7 a c) = (term10 c)).
Proof. exact (MK_COMB (@lem21972 a c) (@lem21973 c)). Qed.
Lemma lem21975 (a : Prop) (c : Prop) : ((term3 c a) = (term9 c)) = ((term7 a c) = (term10 c)).
Proof. exact (TRANS (@lem21969 a c) (@lem21974 a c)). Qed.
Lemma lem21976 (c : Prop) (a : Prop) (h1 : a = False) : (term7 a c) = (term10 c).
Proof. exact (EQ_MP (@lem21975 a c) (@lem21966 c a h1)). Qed.
Lemma lem21977 (c : Prop) (a : Prop) (h1 : a = False) : (term10 c) = (term7 a c).
Proof. exact (SYM (@lem21976 c a h1)). Qed.
Lemma lem21979 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem21980 (c : Prop) : (term5 c) = (term11 c).
Proof. exact (@lem21979 (term11 c)). Qed.
Lemma lem21986 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem21987 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem21988 : term12 = (or False).
Proof. exact (MK_COMB (@lem21987) (@lem21986)). Qed.
Lemma lem21989 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem21990 (c : Prop) : (term13 c) = (False \/ c).
Proof. exact (MK_COMB (@lem21988) (@lem21989 c)). Qed.
Lemma lem21992 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem21993 (c : Prop) : (False \/ c) = c.
Proof. exact (@lem21992 c). Qed.
Lemma lem21994 (c : Prop) : (term13 c) = c.
Proof. exact (TRANS (@lem21990 c) (@lem21993 c)). Qed.
Lemma lem21995 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem21996 (c : Prop) : (term14 c) = (imp c).
Proof. exact (MK_COMB (@lem21995) (@lem21994 c)). Qed.
Lemma lem21997 (c : Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem21998 (c : Prop) : (term11 c) = (c -> c).
Proof. exact (MK_COMB (@lem21996 c) (@lem21997 c)). Qed.
Lemma lem22000 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem22001 (c : Prop) : (c -> c) = True.
Proof. exact (@lem22000 c). Qed.
Lemma lem22002 (c : Prop) : (term11 c) = True.
Proof. exact (TRANS (@lem21998 c) (@lem22001 c)). Qed.
Lemma lem22003 (c : Prop) : (term5 c) = True.
Proof. exact (TRANS (@lem21980 c) (@lem22002 c)). Qed.
Lemma lem22004 (c : Prop) : True = (term5 c).
Proof. exact (SYM (@lem22003 c)). Qed.
Lemma lem22005 (c : Prop) : term5 c.
Proof. exact (EQ_MP (@lem22004 c) (@lem0)). Qed.
Lemma lem22007 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem22008 (c : Prop) : (term10 c) = True.
Proof. exact (@lem22007 (term15 c)). Qed.
Lemma lem22009 (c : Prop) : True = (term10 c).
Proof. exact (SYM (@lem22008 c)). Qed.
Lemma lem22010 (c : Prop) : term10 c.
Proof. exact (EQ_MP (@lem22009 c) (@lem0)). Qed.
Lemma lem22011 (c : Prop) (a : Prop) (h1 : a = False) : term7 a c.
Proof. exact (EQ_MP (@lem21977 c a h1) (@lem22010 c)). Qed.
Lemma lem22012 (c : Prop) (a : Prop) (h1 : a = True) : term7 a c.
Proof. exact (EQ_MP (@lem21964 c a h1) (@lem22005 c)). Qed.
Lemma lem22015 (a : Prop) (c : Prop) : term7 a c.
Proof. exact (or_elim (@lem21941 a) (fun h0 : a = True => @lem22012 c a h0) (fun h0 : a = False => @lem22011 c a h0)). Qed.
Lemma lem22020 (a : Prop) : term16 a.
Proof. exact (fun c : Prop => @lem22015 a c). Qed.
Lemma lem22025 : term17.
Proof. exact (fun a : Prop => @lem22020 a). Qed.
