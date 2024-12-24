Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1097080_term_abbrevs.
Require Import thm1096681_spec.
Require Import thm1097035_spec.
Lemma lem1097036 {A : Type'} : (term0 A) = (term1 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1097037 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem1097036 A) (@lem1096681 A)). Qed.
Lemma lem1097038 {A : Type'} : term2 A.
Proof. exact (@lem1097037 A term3). Qed.
Lemma lem1097039 {A : Type'} : (term2 A) = (term4 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem1097040 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1097039 A) (@lem1097038 A)). Qed.
Lemma lem1097041 {A : Type'} (h1 : (@List.length A) = (term5 A)) : (@List.length A) = (term5 A).
Proof. exact (h1). Qed.
Lemma lem1097042 {A : Type'} (h1 : (@List.length A) = (term5 A)) : (term5 A) = (@List.length A).
Proof. exact (SYM (@lem1097041 A h1)). Qed.
Lemma lem1097043 {A : Type'} (h1 : (term5 A) = (@List.length A)) : (term5 A) = (@List.length A).
Proof. exact (h1). Qed.
Lemma lem1097044 {A : Type'} (h1 : (term5 A) = (@List.length A)) : (@List.length A) = (term5 A).
Proof. exact (SYM (@lem1097043 A h1)). Qed.
Lemma lem1097045 {A : Type'} : ((@List.length A) = (term5 A)) = ((term5 A) = (@List.length A)).
Proof. exact (prop_ext (fun h1 : (@List.length A) = (term5 A) => @lem1097042 A h1) (fun h1 : (term5 A) = (@List.length A) => @lem1097044 A h1)). Qed.
Lemma lem1097048 {A : Type'} : (term5 A) = (@List.length A).
Proof. exact (EQ_MP (@lem1097045 A) (@lem1097035 A)). Qed.
Lemma lem1097049 {A : Type'} : (term5 A) = (@List.length A).
Proof. exact (@lem1097048 A). Qed.
Lemma lem1097050 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1097051 {A : Type'} : (term6 A) = (@List.length A (@nil A)).
Proof. exact (MK_COMB (@lem1097049 A) (@lem1097050 A)). Qed.
Lemma lem1097052 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1097053 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (MK_COMB (@lem1097052) (@lem1097051 A)). Qed.
Lemma lem1097054 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1097055 {A : Type'} : ((term6 A) = (NUMERAL 0)) = ((@List.length A (@nil A)) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1097053 A) (@lem1097054)). Qed.
Lemma lem1097056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1097057 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem1097056) (@lem1097055 A)). Qed.
Lemma lem1097059 {A : Type'} : (term5 A) = (@List.length A).
Proof. exact (EQ_MP (@lem1097045 A) (@lem1097035 A)). Qed.
Lemma lem1097060 {A : Type'} : (term5 A) = (@List.length A).
Proof. exact (@lem1097059 A). Qed.
Lemma lem1097061 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem1097062 {A : Type'} (h : A) (t : list A) : (term11 A h t) = (term12 A h t).
Proof. exact (MK_COMB (@lem1097060 A) (@lem1097061 A h t)). Qed.
Lemma lem1097063 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1097064 {A : Type'} (h : A) (t : list A) : (term13 A h t) = (term14 A h t).
Proof. exact (MK_COMB (@lem1097063) (@lem1097062 A h t)). Qed.
Lemma lem1097066 {A : Type'} : (term5 A) = (@List.length A).
Proof. exact (EQ_MP (@lem1097045 A) (@lem1097035 A)). Qed.
Lemma lem1097067 {A : Type'} : (term5 A) = (@List.length A).
Proof. exact (@lem1097066 A). Qed.
Lemma lem1097068 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1097069 {A : Type'} (t : list A) : (term15 A t) = (@List.length A t).
Proof. exact (MK_COMB (@lem1097067 A) (@lem1097068 A t)). Qed.
Lemma lem1097070 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1097071 {A : Type'} (t : list A) : (term16 A t) = (term17 A t).
Proof. exact (MK_COMB (@lem1097070) (@lem1097069 A t)). Qed.
Lemma lem1097072 {A : Type'} (h : A) (t : list A) : ((term11 A h t) = (term16 A t)) = ((term12 A h t) = (term17 A t)).
Proof. exact (MK_COMB (@lem1097064 A h t) (@lem1097071 A t)). Qed.
Lemma lem1097073 {A : Type'} (h : A) : (term18 A h) = (term19 A h).
Proof. exact (fun_ext (fun t : list A => @lem1097072 A h t)). Qed.
Lemma lem1097074 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1097075 {A : Type'} (h : A) : (term20 A h) = (term21 A h).
Proof. exact (MK_COMB (@lem1097074 A) (@lem1097073 A h)). Qed.
Lemma lem1097076 {A : Type'} : (term22 A) = (term23 A).
Proof. exact (fun_ext (fun h : A => @lem1097075 A h)). Qed.
Lemma lem1097077 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1097078 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (MK_COMB (@lem1097077 A) (@lem1097076 A)). Qed.
Lemma lem1097079 {A : Type'} : (term4 A) = (term26 A).
Proof. exact (MK_COMB (@lem1097057 A) (@lem1097078 A)). Qed.
Lemma lem1097080 {A : Type'} : term26 A.
Proof. exact (EQ_MP (@lem1097079 A) (@lem1097040 A)). Qed.
