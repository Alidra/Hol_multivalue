Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1095962_term_abbrevs.
Require Import thm1095555_spec.
Require Import thm1095905_spec.
Lemma lem1095906 {A : Type'} : (term0 A) = (term1 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1095907 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem1095906 A) (@lem1095555 A)). Qed.
Lemma lem1095908 {A : Type'} : term2 A.
Proof. exact (@lem1095907 A term3). Qed.
Lemma lem1095909 {A : Type'} : (term2 A) = (term4 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem1095910 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1095909 A) (@lem1095908 A)). Qed.
Lemma lem1095911 {A : Type'} (h1 : (@List.app A) = (term5 A)) : (@List.app A) = (term5 A).
Proof. exact (h1). Qed.
Lemma lem1095912 {A : Type'} (h1 : (@List.app A) = (term5 A)) : (term5 A) = (@List.app A).
Proof. exact (SYM (@lem1095911 A h1)). Qed.
Lemma lem1095913 {A : Type'} (h1 : (term5 A) = (@List.app A)) : (term5 A) = (@List.app A).
Proof. exact (h1). Qed.
Lemma lem1095914 {A : Type'} (h1 : (term5 A) = (@List.app A)) : (@List.app A) = (term5 A).
Proof. exact (SYM (@lem1095913 A h1)). Qed.
Lemma lem1095915 {A : Type'} : ((@List.app A) = (term5 A)) = ((term5 A) = (@List.app A)).
Proof. exact (prop_ext (fun h1 : (@List.app A) = (term5 A) => @lem1095912 A h1) (fun h1 : (term5 A) = (@List.app A) => @lem1095914 A h1)). Qed.
Lemma lem1095918 {A : Type'} : (term5 A) = (@List.app A).
Proof. exact (EQ_MP (@lem1095915 A) (@lem1095905 A)). Qed.
Lemma lem1095919 {A : Type'} : (term5 A) = (@List.app A).
Proof. exact (@lem1095918 A). Qed.
Lemma lem1095920 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1095921 {A : Type'} : (term6 A) = (@List.app A (@nil A)).
Proof. exact (MK_COMB (@lem1095919 A) (@lem1095920 A)). Qed.
Lemma lem1095922 {A : Type'} (l : list A) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1095923 {A : Type'} (l : list A) : (term7 A l) = (@List.app A (@nil A) l).
Proof. exact (MK_COMB (@lem1095921 A) (@lem1095922 A l)). Qed.
Lemma lem1095924 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1095925 {A : Type'} (l : list A) : (term8 A l) = (term9 A l).
Proof. exact (MK_COMB (@lem1095924 A) (@lem1095923 A l)). Qed.
Lemma lem1095926 {A : Type'} (l : list A) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1095927 {A : Type'} (l : list A) : ((term7 A l) = l) = ((@List.app A (@nil A) l) = l).
Proof. exact (MK_COMB (@lem1095925 A l) (@lem1095926 A l)). Qed.
Lemma lem1095928 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (fun_ext (fun l : list A => @lem1095927 A l)). Qed.
Lemma lem1095929 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1095930 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (MK_COMB (@lem1095929 A) (@lem1095928 A)). Qed.
Lemma lem1095931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1095932 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem1095931) (@lem1095930 A)). Qed.
Lemma lem1095934 {A : Type'} : (term5 A) = (@List.app A).
Proof. exact (EQ_MP (@lem1095915 A) (@lem1095905 A)). Qed.
Lemma lem1095935 {A : Type'} : (term5 A) = (@List.app A).
Proof. exact (@lem1095934 A). Qed.
Lemma lem1095936 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem1095937 {A : Type'} (h : A) (t : list A) : (term16 A h t) = (term17 A h t).
Proof. exact (MK_COMB (@lem1095935 A) (@lem1095936 A h t)). Qed.
Lemma lem1095938 {A : Type'} (l : list A) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1095939 {A : Type'} (h : A) (t : list A) (l : list A) : (term18 A h t l) = (term19 A h t l).
Proof. exact (MK_COMB (@lem1095937 A h t) (@lem1095938 A l)). Qed.
Lemma lem1095940 {A : Type'} : (@eq (list A)) = (@eq (list A)).
Proof. exact (eq_refl (@eq (list A))). Qed.
Lemma lem1095941 {A : Type'} (h : A) (t : list A) (l : list A) : (term20 A h t l) = (term21 A h t l).
Proof. exact (MK_COMB (@lem1095940 A) (@lem1095939 A h t l)). Qed.
Lemma lem1095943 {A : Type'} : (term5 A) = (@List.app A).
Proof. exact (EQ_MP (@lem1095915 A) (@lem1095905 A)). Qed.
Lemma lem1095944 {A : Type'} : (term5 A) = (@List.app A).
Proof. exact (@lem1095943 A). Qed.
Lemma lem1095945 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1095946 {A : Type'} (t : list A) : (term22 A t) = (@List.app A t).
Proof. exact (MK_COMB (@lem1095944 A) (@lem1095945 A t)). Qed.
Lemma lem1095947 {A : Type'} (l : list A) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1095948 {A : Type'} (t : list A) (l : list A) : (term23 A t l) = (@List.app A t l).
Proof. exact (MK_COMB (@lem1095946 A t) (@lem1095947 A l)). Qed.
Lemma lem1095949 {A : Type'} (h : A) : (@cons A h) = (@cons A h).
Proof. exact (eq_refl (@cons A h)). Qed.
Lemma lem1095950 {A : Type'} (h : A) (t : list A) (l : list A) : (term24 A h t l) = (term25 A h t l).
Proof. exact (MK_COMB (@lem1095949 A h) (@lem1095948 A t l)). Qed.
Lemma lem1095951 {A : Type'} (h : A) (t : list A) (l : list A) : ((term18 A h t l) = (term24 A h t l)) = ((term19 A h t l) = (term25 A h t l)).
Proof. exact (MK_COMB (@lem1095941 A h t l) (@lem1095950 A h t l)). Qed.
Lemma lem1095952 {A : Type'} (h : A) (t : list A) : (term26 A h t) = (term27 A h t).
Proof. exact (fun_ext (fun l : list A => @lem1095951 A h t l)). Qed.
Lemma lem1095953 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1095954 {A : Type'} (h : A) (t : list A) : (term28 A h t) = (term29 A h t).
Proof. exact (MK_COMB (@lem1095953 A) (@lem1095952 A h t)). Qed.
Lemma lem1095955 {A : Type'} (h : A) : (term30 A h) = (term31 A h).
Proof. exact (fun_ext (fun t : list A => @lem1095954 A h t)). Qed.
Lemma lem1095956 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1095957 {A : Type'} (h : A) : (term32 A h) = (term33 A h).
Proof. exact (MK_COMB (@lem1095956 A) (@lem1095955 A h)). Qed.
Lemma lem1095958 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (fun_ext (fun h : A => @lem1095957 A h)). Qed.
Lemma lem1095959 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1095960 {A : Type'} : (term36 A) = (term37 A).
Proof. exact (MK_COMB (@lem1095959 A) (@lem1095958 A)). Qed.
Lemma lem1095961 {A : Type'} : (term4 A) = (term38 A).
Proof. exact (MK_COMB (@lem1095932 A) (@lem1095960 A)). Qed.
Lemma lem1095962 {A : Type'} : term38 A.
Proof. exact (EQ_MP (@lem1095961 A) (@lem1095910 A)). Qed.
