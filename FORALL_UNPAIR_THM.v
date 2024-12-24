Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_UNPAIR_THM_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48213_spec.
Require Import thm48214_spec.
Require Import thm48219_spec.
Require Import thm48220_spec.
Lemma lem53847 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term0 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem53848 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term0 _5106 _5107 P) = ((term1 _5106 _5107 P) = (term2 _5106 _5107 P)).
Proof. exact (eq_refl (term0 _5106 _5107 P)). Qed.
Lemma lem53875 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term1 _5106 _5107 P) = (term2 _5106 _5107 P).
Proof. exact (EQ_MP (@lem53848 _5106 _5107 P) (@lem53847 _5106 _5107 P)). Qed.
Lemma lem53876 {_5486 _5488 : Type'} (P : type1210 _5486 _5488) : (term3 _5486 _5488 P) = (term4 _5486 _5488 P).
Proof. exact (@lem53875 _5488 _5486 P). Qed.
Lemma lem53877 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term5 _5486 _5488 P) = (term6 _5486 _5488 P).
Proof. exact (@lem53876 _5486 _5488 (term7 _5486 _5488 P)). Qed.
Lemma lem53878 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) (z : prod _5486 _5488) : (term8 _5486 _5488 P z) = (term9 _5486 _5488 P z).
Proof. exact (eq_refl (term8 _5486 _5488 P z)). Qed.
Lemma lem53879 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term10 _5486 _5488 P) = (term7 _5486 _5488 P).
Proof. exact (fun_ext (fun z : prod _5486 _5488 => @lem53878 _5486 _5488 P z)). Qed.
Lemma lem53880 {_5486 _5488 : Type'} : (@all (prod _5486 _5488)) = (@all (prod _5486 _5488)).
Proof. exact (eq_refl (@all (prod _5486 _5488))). Qed.
Lemma lem53881 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term5 _5486 _5488 P) = (term11 _5486 _5488 P).
Proof. exact (MK_COMB (@lem53880 _5486 _5488) (@lem53879 _5486 _5488 P)). Qed.
Lemma lem53882 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem53883 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term12 _5486 _5488 P) = (term13 _5486 _5488 P).
Proof. exact (MK_COMB (@lem53882) (@lem53881 _5486 _5488 P)). Qed.
Lemma lem53884 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) (p1 : _5486) (p2 : _5488) : (term14 _5486 _5488 P p1 p2) = (term15 _5486 _5488 P p1 p2).
Proof. exact (eq_refl (term14 _5486 _5488 P p1 p2)). Qed.
Lemma lem53885 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) (p1 : _5486) : (term16 _5486 _5488 P p1) = (term17 _5486 _5488 P p1).
Proof. exact (fun_ext (fun p2 : _5488 => @lem53884 _5486 _5488 P p1 p2)). Qed.
Lemma lem53886 {_5488 : Type'} : (@all _5488) = (@all _5488).
Proof. exact (eq_refl (@all _5488)). Qed.
Lemma lem53887 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) (p1 : _5486) : (term18 _5486 _5488 P p1) = (term19 _5486 _5488 P p1).
Proof. exact (MK_COMB (@lem53886 _5488) (@lem53885 _5486 _5488 P p1)). Qed.
Lemma lem53888 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term20 _5486 _5488 P) = (term21 _5486 _5488 P).
Proof. exact (fun_ext (fun p1 : _5486 => @lem53887 _5486 _5488 P p1)). Qed.
Lemma lem53889 {_5486 : Type'} : (@all _5486) = (@all _5486).
Proof. exact (eq_refl (@all _5486)). Qed.
Lemma lem53890 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term6 _5486 _5488 P) = (term22 _5486 _5488 P).
Proof. exact (MK_COMB (@lem53889 _5486) (@lem53888 _5486 _5488 P)). Qed.
Lemma lem53891 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : ((term5 _5486 _5488 P) = (term6 _5486 _5488 P)) = ((term11 _5486 _5488 P) = (term22 _5486 _5488 P)).
Proof. exact (MK_COMB (@lem53883 _5486 _5488 P) (@lem53890 _5486 _5488 P)). Qed.
Lemma lem53892 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term11 _5486 _5488 P) = (term22 _5486 _5488 P).
Proof. exact (EQ_MP (@lem53891 _5486 _5488 P) (@lem53877 _5486 _5488 P)). Qed.
Lemma lem53906 {A B : Type'} (y : B) (x : A) : (term23 A B x y) = x.
Proof. exact (EQ_MP (@lem48220 A B y x) (@lem48219 A B x y)). Qed.
Lemma lem53907 {_5486 _5488 : Type'} (y : _5488) (x : _5486) : (term23 _5486 _5488 x y) = x.
Proof. exact (@lem53906 _5486 _5488 y x). Qed.
Lemma lem53908 {_5486 _5488 : Type'} (p2 : _5488) (p1 : _5486) : (term23 _5486 _5488 p1 p2) = p1.
Proof. exact (@lem53907 _5486 _5488 p2 p1). Qed.
Lemma lem53909 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem53910 {_5486 _5488 : Type'} (p2 : _5488) (P : type1413 _5486 _5488) (p1 : _5486) : (term24 _5486 _5488 P p1 p2) = (P p1).
Proof. exact (MK_COMB (@lem53909 _5486 _5488 P) (@lem53908 _5486 _5488 p2 p1)). Qed.
Lemma lem53912 {A B : Type'} (x : A) (y : B) : (term25 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem53913 {_5486 _5488 : Type'} (x : _5486) (y : _5488) : (term25 _5486 _5488 x y) = y.
Proof. exact (@lem53912 _5486 _5488 x y). Qed.
Lemma lem53914 {_5486 _5488 : Type'} (p1 : _5486) (p2 : _5488) : (term25 _5486 _5488 p1 p2) = p2.
Proof. exact (@lem53913 _5486 _5488 p1 p2). Qed.
Lemma lem53915 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) (p1 : _5486) (p2 : _5488) : (term15 _5486 _5488 P p1 p2) = (P p1 p2).
Proof. exact (MK_COMB (@lem53910 _5486 _5488 p2 P p1) (@lem53914 _5486 _5488 p1 p2)). Qed.
Lemma lem53916 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) (p1 : _5486) : (term17 _5486 _5488 P p1) = (term26 _5486 _5488 P p1).
Proof. exact (fun_ext (fun p2 : _5488 => @lem53915 _5486 _5488 P p1 p2)). Qed.
Lemma lem53917 {_5488 : Type'} : (@all _5488) = (@all _5488).
Proof. exact (eq_refl (@all _5488)). Qed.
Lemma lem53918 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) (p1 : _5486) : (term19 _5486 _5488 P p1) = (term27 _5486 _5488 P p1).
Proof. exact (MK_COMB (@lem53917 _5488) (@lem53916 _5486 _5488 P p1)). Qed.
Lemma lem53925 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term21 _5486 _5488 P) = (term28 _5486 _5488 P).
Proof. exact (fun_ext (fun p1 : _5486 => @lem53918 _5486 _5488 P p1)). Qed.
Lemma lem53926 {_5486 : Type'} : (@all _5486) = (@all _5486).
Proof. exact (eq_refl (@all _5486)). Qed.
Lemma lem53927 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term22 _5486 _5488 P) = (term29 _5486 _5488 P).
Proof. exact (MK_COMB (@lem53926 _5486) (@lem53925 _5486 _5488 P)). Qed.
Lemma lem53934 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term11 _5486 _5488 P) = (term29 _5486 _5488 P).
Proof. exact (TRANS (@lem53892 _5486 _5488 P) (@lem53927 _5486 _5488 P)). Qed.
Lemma lem53935 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term30 _5486 _5488 P) = (term30 _5486 _5488 P).
Proof. exact (eq_refl (term30 _5486 _5488 P)). Qed.
Lemma lem53936 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : ((term29 _5486 _5488 P) = (term11 _5486 _5488 P)) = ((term29 _5486 _5488 P) = (term29 _5486 _5488 P)).
Proof. exact (MK_COMB (@lem53935 _5486 _5488 P) (@lem53934 _5486 _5488 P)). Qed.
Lemma lem53938 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem53939 (x : Prop) : (x = x) = True.
Proof. exact (@lem53938 Prop x). Qed.
Lemma lem53940 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : ((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True.
Proof. exact (@lem53939 (term29 _5486 _5488 P)). Qed.
Lemma lem53943 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term31 _5486 _5488 P) = (term31 _5486 _5488 P).
Proof. exact (eq_refl (term31 _5486 _5488 P)). Qed.
Lemma lem53944 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term31 _5486 _5488 P) = (((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True).
Proof. exact (eq_refl (term31 _5486 _5488 P)). Qed.
Lemma lem53945 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term32 _5486 _5488 P) = (term32 _5486 _5488 P).
Proof. exact (eq_refl (term32 _5486 _5488 P)). Qed.
Lemma lem53946 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : ((term31 _5486 _5488 P) = (term31 _5486 _5488 P)) = ((term31 _5486 _5488 P) = (((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True)).
Proof. exact (MK_COMB (@lem53945 _5486 _5488 P) (@lem53944 _5486 _5488 P)). Qed.
Lemma lem53947 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term31 _5486 _5488 P) = (((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True).
Proof. exact (eq_refl (term31 _5486 _5488 P)). Qed.
Lemma lem53948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem53949 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (term32 _5486 _5488 P) = (term33 _5486 _5488 P).
Proof. exact (MK_COMB (@lem53948) (@lem53947 _5486 _5488 P)). Qed.
Lemma lem53950 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True) = (((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True).
Proof. exact (eq_refl (((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True)). Qed.
Lemma lem53951 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : ((term31 _5486 _5488 P) = (((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True)) = ((((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True) = (((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True)).
Proof. exact (MK_COMB (@lem53949 _5486 _5488 P) (@lem53950 _5486 _5488 P)). Qed.
Lemma lem53952 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : ((term31 _5486 _5488 P) = (term31 _5486 _5488 P)) = ((((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True) = (((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True)).
Proof. exact (TRANS (@lem53946 _5486 _5488 P) (@lem53951 _5486 _5488 P)). Qed.
Lemma lem53953 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : (((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True) = (((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True).
Proof. exact (EQ_MP (@lem53952 _5486 _5488 P) (@lem53943 _5486 _5488 P)). Qed.
Lemma lem53954 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : ((term29 _5486 _5488 P) = (term29 _5486 _5488 P)) = True.
Proof. exact (EQ_MP (@lem53953 _5486 _5488 P) (@lem53940 _5486 _5488 P)). Qed.
Lemma lem53955 {_5486 _5488 : Type'} (P : type1413 _5486 _5488) : ((term29 _5486 _5488 P) = (term11 _5486 _5488 P)) = True.
Proof. exact (TRANS (@lem53936 _5486 _5488 P) (@lem53954 _5486 _5488 P)). Qed.
Lemma lem53956 {_5486 _5488 : Type'} : (term34 _5486 _5488) = (term35 _5486 _5488).
Proof. exact (fun_ext (fun P : type1413 _5486 _5488 => @lem53955 _5486 _5488 P)). Qed.
Lemma lem53957 {_5486 _5488 : Type'} : (@all (_5486 -> _5488 -> Prop)) = (@all (_5486 -> _5488 -> Prop)).
Proof. exact (eq_refl (@all (_5486 -> _5488 -> Prop))). Qed.
Lemma lem53958 {_5486 _5488 : Type'} : (term36 _5486 _5488) = (term37 _5486 _5488).
Proof. exact (MK_COMB (@lem53957 _5486 _5488) (@lem53956 _5486 _5488)). Qed.
Lemma lem53960 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem53961 {_5486 _5488 : Type'} (t : Prop) : (term39 _5486 _5488 t) = t.
Proof. exact (@lem53960 (type1413 _5486 _5488) t). Qed.
Lemma lem53962 {_5486 _5488 : Type'} : (term37 _5486 _5488) = True.
Proof. exact (@lem53961 _5486 _5488 True). Qed.
Lemma lem53963 {_5486 _5488 : Type'} : (term36 _5486 _5488) = True.
Proof. exact (TRANS (@lem53958 _5486 _5488) (@lem53962 _5486 _5488)). Qed.
Lemma lem53964 {_5486 _5488 : Type'} : True = (term36 _5486 _5488).
Proof. exact (SYM (@lem53963 _5486 _5488)). Qed.
Lemma lem53965 {_5486 _5488 : Type'} : term36 _5486 _5488.
Proof. exact (EQ_MP (@lem53964 _5486 _5488) (@lem0)). Qed.
