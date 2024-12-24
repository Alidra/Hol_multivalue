Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm11004_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem10906 (b : Prop) : term0 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem10907 (b : Prop) : (term0 b) = (term1 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem10908 (b : Prop) : term1 b.
Proof. exact (EQ_MP (@lem10907 b) (@lem10906 b)). Qed.
Lemma lem10909 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem10910 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem10911 (P : Prop -> Prop) (h1 : term2 P) : term2 P.
Proof. exact (h1). Qed.
Lemma lem10912 (P : Prop -> Prop) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem10913 (b : Prop) (P : Prop -> Prop) (h1 : term2 P) : term4 P b.
Proof. exact (@lem10911 P h1 b). Qed.
Lemma lem10914 (P : Prop -> Prop) (b : Prop) : (term4 P b) = (P b).
Proof. exact (eq_refl (term4 P b)). Qed.
Lemma lem10915 (b : Prop) (P : Prop -> Prop) (h1 : term2 P) : P b.
Proof. exact (EQ_MP (@lem10914 P b) (@lem10913 b P h1)). Qed.
Lemma lem10916 (P : Prop -> Prop) (b : Prop) : (P b) = ((P b) = True).
Proof. exact (@lem7 (P b)). Qed.
Lemma lem10921 (b : Prop) (P : Prop -> Prop) (h1 : term2 P) : (P b) = True.
Proof. exact (EQ_MP (@lem10916 P b) (@lem10915 b P h1)). Qed.
Lemma lem10922 (P : Prop -> Prop) (h1 : term2 P) : (P True) = True.
Proof. exact (@lem10921 True P h1). Qed.
Lemma lem10923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem10924 (P : Prop -> Prop) (h1 : term2 P) : (term5 P) = (and True).
Proof. exact (MK_COMB (@lem10923) (@lem10922 P h1)). Qed.
Lemma lem10926 (b : Prop) (P : Prop -> Prop) (h1 : term2 P) : (P b) = True.
Proof. exact (EQ_MP (@lem10916 P b) (@lem10915 b P h1)). Qed.
Lemma lem10927 (P : Prop -> Prop) (h1 : term2 P) : (P False) = True.
Proof. exact (@lem10926 False P h1). Qed.
Lemma lem10928 (P : Prop -> Prop) (h1 : term2 P) : (term3 P) = (True /\ True).
Proof. exact (MK_COMB (@lem10924 P h1) (@lem10927 P h1)). Qed.
Lemma lem10930 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem10931 : (True /\ True) = True.
Proof. exact (@lem10930 True). Qed.
Lemma lem10932 (P : Prop -> Prop) (h1 : term2 P) : (term3 P) = True.
Proof. exact (TRANS (@lem10928 P h1) (@lem10931)). Qed.
Lemma lem10933 (P : Prop -> Prop) (h1 : term2 P) : True = (term3 P).
Proof. exact (SYM (@lem10932 P h1)). Qed.
Lemma lem10934 (P : Prop -> Prop) (h1 : term2 P) : term3 P.
Proof. exact (EQ_MP (@lem10933 P h1) (@lem0)). Qed.
Lemma lem10947 (P : Prop -> Prop) : (term6 P) = (term6 P).
Proof. exact (eq_refl (term6 P)). Qed.
Lemma lem10948 (P : Prop -> Prop) (b : Prop) (h1 : b = True) : (term4 P b) = (term7 P).
Proof. exact (MK_COMB (@lem10947 P) (@lem10909 b h1)). Qed.
Lemma lem10949 (P : Prop -> Prop) : (term7 P) = (P True).
Proof. exact (eq_refl (term7 P)). Qed.
Lemma lem10950 (P : Prop -> Prop) (b : Prop) : (term8 P b) = (term8 P b).
Proof. exact (eq_refl (term8 P b)). Qed.
Lemma lem10951 (b : Prop) (P : Prop -> Prop) : ((term4 P b) = (term7 P)) = ((term4 P b) = (P True)).
Proof. exact (MK_COMB (@lem10950 P b) (@lem10949 P)). Qed.
Lemma lem10952 (P : Prop -> Prop) (b : Prop) : (term4 P b) = (P b).
Proof. exact (eq_refl (term4 P b)). Qed.
Lemma lem10953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10954 (P : Prop -> Prop) (b : Prop) : (term8 P b) = (term9 P b).
Proof. exact (MK_COMB (@lem10953) (@lem10952 P b)). Qed.
Lemma lem10955 (P : Prop -> Prop) : (P True) = (P True).
Proof. exact (eq_refl (P True)). Qed.
Lemma lem10956 (b : Prop) (P : Prop -> Prop) : ((term4 P b) = (P True)) = ((P b) = (P True)).
Proof. exact (MK_COMB (@lem10954 P b) (@lem10955 P)). Qed.
Lemma lem10957 (b : Prop) (P : Prop -> Prop) : ((term4 P b) = (term7 P)) = ((P b) = (P True)).
Proof. exact (TRANS (@lem10951 b P) (@lem10956 b P)). Qed.
Lemma lem10958 (P : Prop -> Prop) (b : Prop) (h1 : b = True) : (P b) = (P True).
Proof. exact (EQ_MP (@lem10957 b P) (@lem10948 P b h1)). Qed.
Lemma lem10959 (P : Prop -> Prop) (b : Prop) (h1 : b = True) : (P True) = (P b).
Proof. exact (SYM (@lem10958 P b h1)). Qed.
Lemma lem10960 (P : Prop -> Prop) : (term6 P) = (term6 P).
Proof. exact (eq_refl (term6 P)). Qed.
Lemma lem10961 (P : Prop -> Prop) (b : Prop) (h1 : b = False) : (term4 P b) = (term10 P).
Proof. exact (MK_COMB (@lem10960 P) (@lem10910 b h1)). Qed.
Lemma lem10962 (P : Prop -> Prop) : (term10 P) = (P False).
Proof. exact (eq_refl (term10 P)). Qed.
Lemma lem10963 (P : Prop -> Prop) (b : Prop) : (term8 P b) = (term8 P b).
Proof. exact (eq_refl (term8 P b)). Qed.
Lemma lem10964 (b : Prop) (P : Prop -> Prop) : ((term4 P b) = (term10 P)) = ((term4 P b) = (P False)).
Proof. exact (MK_COMB (@lem10963 P b) (@lem10962 P)). Qed.
Lemma lem10965 (P : Prop -> Prop) (b : Prop) : (term4 P b) = (P b).
Proof. exact (eq_refl (term4 P b)). Qed.
Lemma lem10966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10967 (P : Prop -> Prop) (b : Prop) : (term8 P b) = (term9 P b).
Proof. exact (MK_COMB (@lem10966) (@lem10965 P b)). Qed.
Lemma lem10968 (P : Prop -> Prop) : (P False) = (P False).
Proof. exact (eq_refl (P False)). Qed.
Lemma lem10969 (b : Prop) (P : Prop -> Prop) : ((term4 P b) = (P False)) = ((P b) = (P False)).
Proof. exact (MK_COMB (@lem10967 P b) (@lem10968 P)). Qed.
Lemma lem10970 (b : Prop) (P : Prop -> Prop) : ((term4 P b) = (term10 P)) = ((P b) = (P False)).
Proof. exact (TRANS (@lem10964 b P) (@lem10969 b P)). Qed.
Lemma lem10971 (P : Prop -> Prop) (b : Prop) (h1 : b = False) : (P b) = (P False).
Proof. exact (EQ_MP (@lem10970 b P) (@lem10961 P b h1)). Qed.
Lemma lem10972 (P : Prop -> Prop) (b : Prop) (h1 : b = False) : (P False) = (P b).
Proof. exact (SYM (@lem10971 P b h1)). Qed.
Lemma lem10976 (P : Prop -> Prop) (h1 : term3 P) : P True.
Proof. exact (proj1 (@lem10912 P h1)). Qed.
Lemma lem10977 (P : Prop -> Prop) : (P True) = ((P True) = True).
Proof. exact (@lem7 (P True)). Qed.
Lemma lem10980 (P : Prop -> Prop) (h1 : term3 P) : (P True) = True.
Proof. exact (EQ_MP (@lem10977 P) (@lem10976 P h1)). Qed.
Lemma lem10981 (P : Prop -> Prop) (h1 : term3 P) : True = (P True).
Proof. exact (SYM (@lem10980 P h1)). Qed.
Lemma lem10982 (P : Prop -> Prop) (h1 : term3 P) : P True.
Proof. exact (EQ_MP (@lem10981 P h1) (@lem0)). Qed.
Lemma lem10983 (P : Prop -> Prop) (h1 : term3 P) : P False.
Proof. exact (proj2 (@lem10912 P h1)). Qed.
Lemma lem10984 (P : Prop -> Prop) : (P False) = ((P False) = True).
Proof. exact (@lem7 (P False)). Qed.
Lemma lem10990 (P : Prop -> Prop) (h1 : term3 P) : (P False) = True.
Proof. exact (EQ_MP (@lem10984 P) (@lem10983 P h1)). Qed.
Lemma lem10991 (P : Prop -> Prop) (h1 : term3 P) : True = (P False).
Proof. exact (SYM (@lem10990 P h1)). Qed.
Lemma lem10992 (P : Prop -> Prop) (h1 : term3 P) : P False.
Proof. exact (EQ_MP (@lem10991 P h1) (@lem0)). Qed.
Lemma lem10993 (P : Prop -> Prop) (b : Prop) (h1 : term3 P) (h2 : b = False) : P b.
Proof. exact (EQ_MP (@lem10972 P b h2) (@lem10992 P h1)). Qed.
Lemma lem10994 (P : Prop -> Prop) (b : Prop) (h1 : term3 P) (h2 : b = True) : P b.
Proof. exact (EQ_MP (@lem10959 P b h2) (@lem10982 P h1)). Qed.
Lemma lem10995 (b : Prop) (P : Prop -> Prop) (h1 : term3 P) : P b.
Proof. exact (or_elim (@lem10908 b) (fun h0 : b = True => @lem10994 P b h1 h0) (fun h0 : b = False => @lem10993 P b h1 h0)). Qed.
Lemma lem11001 (P : Prop -> Prop) (h1 : term3 P) : term2 P.
Proof. exact (fun b : Prop => @lem10995 b P h1). Qed.
Lemma lem11002 (P : Prop -> Prop) : term11 P.
Proof. exact (fun h0 : term3 P => @lem11001 P h0). Qed.
Lemma lem11003 (P : Prop -> Prop) : term12 P.
Proof. exact (fun h0 : term2 P => @lem10934 P h0). Qed.
Lemma lem11004 (P : Prop -> Prop) : term13 P.
Proof. exact (conj (@lem11003 P) (@lem11002 P)). Qed.
