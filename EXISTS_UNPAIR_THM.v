Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_UNPAIR_THM_term_abbrevs.
Require Import EXISTS_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48213_spec.
Require Import thm48214_spec.
Require Import thm48219_spec.
Require Import thm48220_spec.
Lemma lem53988 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : term0 _5131 _5132 P.
Proof. exact (@lem51006 _5131 _5132 P). Qed.
Lemma lem53989 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term0 _5131 _5132 P) = ((term1 _5131 _5132 P) = (term2 _5131 _5132 P)).
Proof. exact (eq_refl (term0 _5131 _5132 P)). Qed.
Lemma lem54014 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term1 _5131 _5132 P) = (term2 _5131 _5132 P).
Proof. exact (EQ_MP (@lem53989 _5131 _5132 P) (@lem53988 _5131 _5132 P)). Qed.
Lemma lem54015 {_5515 _5517 : Type'} (P : type1210 _5515 _5517) : (term3 _5515 _5517 P) = (term4 _5515 _5517 P).
Proof. exact (@lem54014 _5517 _5515 P). Qed.
Lemma lem54016 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term5 _5515 _5517 P) = (term6 _5515 _5517 P).
Proof. exact (@lem54015 _5515 _5517 (term7 _5515 _5517 P)). Qed.
Lemma lem54017 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) (z : prod _5515 _5517) : (term8 _5515 _5517 P z) = (term9 _5515 _5517 P z).
Proof. exact (eq_refl (term8 _5515 _5517 P z)). Qed.
Lemma lem54018 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term10 _5515 _5517 P) = (term7 _5515 _5517 P).
Proof. exact (fun_ext (fun z : prod _5515 _5517 => @lem54017 _5515 _5517 P z)). Qed.
Lemma lem54019 {_5515 _5517 : Type'} : (@ex (prod _5515 _5517)) = (@ex (prod _5515 _5517)).
Proof. exact (eq_refl (@ex (prod _5515 _5517))). Qed.
Lemma lem54020 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term5 _5515 _5517 P) = (term11 _5515 _5517 P).
Proof. exact (MK_COMB (@lem54019 _5515 _5517) (@lem54018 _5515 _5517 P)). Qed.
Lemma lem54021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem54022 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term12 _5515 _5517 P) = (term13 _5515 _5517 P).
Proof. exact (MK_COMB (@lem54021) (@lem54020 _5515 _5517 P)). Qed.
Lemma lem54023 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) (p1 : _5515) (p2 : _5517) : (term14 _5515 _5517 P p1 p2) = (term15 _5515 _5517 P p1 p2).
Proof. exact (eq_refl (term14 _5515 _5517 P p1 p2)). Qed.
Lemma lem54024 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) (p1 : _5515) : (term16 _5515 _5517 P p1) = (term17 _5515 _5517 P p1).
Proof. exact (fun_ext (fun p2 : _5517 => @lem54023 _5515 _5517 P p1 p2)). Qed.
Lemma lem54025 {_5517 : Type'} : (@ex _5517) = (@ex _5517).
Proof. exact (eq_refl (@ex _5517)). Qed.
Lemma lem54026 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) (p1 : _5515) : (term18 _5515 _5517 P p1) = (term19 _5515 _5517 P p1).
Proof. exact (MK_COMB (@lem54025 _5517) (@lem54024 _5515 _5517 P p1)). Qed.
Lemma lem54027 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term20 _5515 _5517 P) = (term21 _5515 _5517 P).
Proof. exact (fun_ext (fun p1 : _5515 => @lem54026 _5515 _5517 P p1)). Qed.
Lemma lem54028 {_5515 : Type'} : (@ex _5515) = (@ex _5515).
Proof. exact (eq_refl (@ex _5515)). Qed.
Lemma lem54029 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term6 _5515 _5517 P) = (term22 _5515 _5517 P).
Proof. exact (MK_COMB (@lem54028 _5515) (@lem54027 _5515 _5517 P)). Qed.
Lemma lem54030 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : ((term5 _5515 _5517 P) = (term6 _5515 _5517 P)) = ((term11 _5515 _5517 P) = (term22 _5515 _5517 P)).
Proof. exact (MK_COMB (@lem54022 _5515 _5517 P) (@lem54029 _5515 _5517 P)). Qed.
Lemma lem54031 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term11 _5515 _5517 P) = (term22 _5515 _5517 P).
Proof. exact (EQ_MP (@lem54030 _5515 _5517 P) (@lem54016 _5515 _5517 P)). Qed.
Lemma lem54045 {A B : Type'} (y : B) (x : A) : (term23 A B x y) = x.
Proof. exact (EQ_MP (@lem48220 A B y x) (@lem48219 A B x y)). Qed.
Lemma lem54046 {_5515 _5517 : Type'} (y : _5517) (x : _5515) : (term23 _5515 _5517 x y) = x.
Proof. exact (@lem54045 _5515 _5517 y x). Qed.
Lemma lem54047 {_5515 _5517 : Type'} (p2 : _5517) (p1 : _5515) : (term23 _5515 _5517 p1 p2) = p1.
Proof. exact (@lem54046 _5515 _5517 p2 p1). Qed.
Lemma lem54048 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem54049 {_5515 _5517 : Type'} (p2 : _5517) (P : type1413 _5515 _5517) (p1 : _5515) : (term24 _5515 _5517 P p1 p2) = (P p1).
Proof. exact (MK_COMB (@lem54048 _5515 _5517 P) (@lem54047 _5515 _5517 p2 p1)). Qed.
Lemma lem54051 {A B : Type'} (x : A) (y : B) : (term25 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem54052 {_5515 _5517 : Type'} (x : _5515) (y : _5517) : (term25 _5515 _5517 x y) = y.
Proof. exact (@lem54051 _5515 _5517 x y). Qed.
Lemma lem54053 {_5515 _5517 : Type'} (p1 : _5515) (p2 : _5517) : (term25 _5515 _5517 p1 p2) = p2.
Proof. exact (@lem54052 _5515 _5517 p1 p2). Qed.
Lemma lem54054 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) (p1 : _5515) (p2 : _5517) : (term15 _5515 _5517 P p1 p2) = (P p1 p2).
Proof. exact (MK_COMB (@lem54049 _5515 _5517 p2 P p1) (@lem54053 _5515 _5517 p1 p2)). Qed.
Lemma lem54055 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) (p1 : _5515) : (term17 _5515 _5517 P p1) = (term26 _5515 _5517 P p1).
Proof. exact (fun_ext (fun p2 : _5517 => @lem54054 _5515 _5517 P p1 p2)). Qed.
Lemma lem54056 {_5517 : Type'} : (@ex _5517) = (@ex _5517).
Proof. exact (eq_refl (@ex _5517)). Qed.
Lemma lem54057 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) (p1 : _5515) : (term19 _5515 _5517 P p1) = (term27 _5515 _5517 P p1).
Proof. exact (MK_COMB (@lem54056 _5517) (@lem54055 _5515 _5517 P p1)). Qed.
Lemma lem54064 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term21 _5515 _5517 P) = (term28 _5515 _5517 P).
Proof. exact (fun_ext (fun p1 : _5515 => @lem54057 _5515 _5517 P p1)). Qed.
Lemma lem54065 {_5515 : Type'} : (@ex _5515) = (@ex _5515).
Proof. exact (eq_refl (@ex _5515)). Qed.
Lemma lem54066 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term22 _5515 _5517 P) = (term29 _5515 _5517 P).
Proof. exact (MK_COMB (@lem54065 _5515) (@lem54064 _5515 _5517 P)). Qed.
Lemma lem54073 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term11 _5515 _5517 P) = (term29 _5515 _5517 P).
Proof. exact (TRANS (@lem54031 _5515 _5517 P) (@lem54066 _5515 _5517 P)). Qed.
Lemma lem54074 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term30 _5515 _5517 P) = (term30 _5515 _5517 P).
Proof. exact (eq_refl (term30 _5515 _5517 P)). Qed.
Lemma lem54075 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : ((term29 _5515 _5517 P) = (term11 _5515 _5517 P)) = ((term29 _5515 _5517 P) = (term29 _5515 _5517 P)).
Proof. exact (MK_COMB (@lem54074 _5515 _5517 P) (@lem54073 _5515 _5517 P)). Qed.
Lemma lem54077 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem54078 (x : Prop) : (x = x) = True.
Proof. exact (@lem54077 Prop x). Qed.
Lemma lem54079 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : ((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True.
Proof. exact (@lem54078 (term29 _5515 _5517 P)). Qed.
Lemma lem54082 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term31 _5515 _5517 P) = (term31 _5515 _5517 P).
Proof. exact (eq_refl (term31 _5515 _5517 P)). Qed.
Lemma lem54083 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term31 _5515 _5517 P) = (((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True).
Proof. exact (eq_refl (term31 _5515 _5517 P)). Qed.
Lemma lem54084 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term32 _5515 _5517 P) = (term32 _5515 _5517 P).
Proof. exact (eq_refl (term32 _5515 _5517 P)). Qed.
Lemma lem54085 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : ((term31 _5515 _5517 P) = (term31 _5515 _5517 P)) = ((term31 _5515 _5517 P) = (((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True)).
Proof. exact (MK_COMB (@lem54084 _5515 _5517 P) (@lem54083 _5515 _5517 P)). Qed.
Lemma lem54086 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term31 _5515 _5517 P) = (((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True).
Proof. exact (eq_refl (term31 _5515 _5517 P)). Qed.
Lemma lem54087 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem54088 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (term32 _5515 _5517 P) = (term33 _5515 _5517 P).
Proof. exact (MK_COMB (@lem54087) (@lem54086 _5515 _5517 P)). Qed.
Lemma lem54089 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True) = (((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True).
Proof. exact (eq_refl (((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True)). Qed.
Lemma lem54090 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : ((term31 _5515 _5517 P) = (((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True)) = ((((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True) = (((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True)).
Proof. exact (MK_COMB (@lem54088 _5515 _5517 P) (@lem54089 _5515 _5517 P)). Qed.
Lemma lem54091 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : ((term31 _5515 _5517 P) = (term31 _5515 _5517 P)) = ((((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True) = (((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True)).
Proof. exact (TRANS (@lem54085 _5515 _5517 P) (@lem54090 _5515 _5517 P)). Qed.
Lemma lem54092 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : (((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True) = (((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True).
Proof. exact (EQ_MP (@lem54091 _5515 _5517 P) (@lem54082 _5515 _5517 P)). Qed.
Lemma lem54093 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : ((term29 _5515 _5517 P) = (term29 _5515 _5517 P)) = True.
Proof. exact (EQ_MP (@lem54092 _5515 _5517 P) (@lem54079 _5515 _5517 P)). Qed.
Lemma lem54094 {_5515 _5517 : Type'} (P : type1413 _5515 _5517) : ((term29 _5515 _5517 P) = (term11 _5515 _5517 P)) = True.
Proof. exact (TRANS (@lem54075 _5515 _5517 P) (@lem54093 _5515 _5517 P)). Qed.
Lemma lem54095 {_5515 _5517 : Type'} : (term34 _5515 _5517) = (term35 _5515 _5517).
Proof. exact (fun_ext (fun P : type1413 _5515 _5517 => @lem54094 _5515 _5517 P)). Qed.
Lemma lem54096 {_5515 _5517 : Type'} : (@all (_5515 -> _5517 -> Prop)) = (@all (_5515 -> _5517 -> Prop)).
Proof. exact (eq_refl (@all (_5515 -> _5517 -> Prop))). Qed.
Lemma lem54097 {_5515 _5517 : Type'} : (term36 _5515 _5517) = (term37 _5515 _5517).
Proof. exact (MK_COMB (@lem54096 _5515 _5517) (@lem54095 _5515 _5517)). Qed.
Lemma lem54099 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem54100 {_5515 _5517 : Type'} (t : Prop) : (term39 _5515 _5517 t) = t.
Proof. exact (@lem54099 (type1413 _5515 _5517) t). Qed.
Lemma lem54101 {_5515 _5517 : Type'} : (term37 _5515 _5517) = True.
Proof. exact (@lem54100 _5515 _5517 True). Qed.
Lemma lem54102 {_5515 _5517 : Type'} : (term36 _5515 _5517) = True.
Proof. exact (TRANS (@lem54097 _5515 _5517) (@lem54101 _5515 _5517)). Qed.
Lemma lem54103 {_5515 _5517 : Type'} : True = (term36 _5515 _5517).
Proof. exact (SYM (@lem54102 _5515 _5517)). Qed.
Lemma lem54104 {_5515 _5517 : Type'} : term36 _5515 _5517.
Proof. exact (EQ_MP (@lem54103 _5515 _5517) (@lem0)). Qed.
