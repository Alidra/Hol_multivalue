Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338076_term_abbrevs.
Require Import TREAL_EQ_REFL_spec.
Require Import TREAL_EQ_TRANS_spec.
Require Import TREAL_INV_WELLDEF_spec.
Require Import thm1337493_spec.
Require Import thm32_spec.
Require Import thm9127_spec.
Lemma lem1337992 : real_inv = term0.
Proof. exact (@real_inv_def). Qed.
Lemma lem1337993 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1337994 (x : real) : (real_inv x) = (term1 x).
Proof. exact (MK_COMB (@lem1337992) (@lem1337993 x)). Qed.
Lemma lem1337995 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1337996 (x : real) : (term3 x) = (term3 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1337997 (x : real) : ((real_inv x) = (term1 x)) = ((real_inv x) = (term2 x)).
Proof. exact (MK_COMB (@lem1337996 x) (@lem1337995 x)). Qed.
Lemma lem1337998 (x : real) : (real_inv x) = (term2 x).
Proof. exact (EQ_MP (@lem1337997 x) (@lem1337994 x)). Qed.
Lemma lem1337999 (x : prod hreal hreal) : (term4 x) = ((term5 x) = (treal_eq x)).
Proof. exact (@lem1337493 (treal_eq x)). Qed.
Lemma lem1338000 (x : prod hreal hreal) : (treal_eq x) = (treal_eq x).
Proof. exact (eq_refl (treal_eq x)). Qed.
Lemma lem1338001 (x : prod hreal hreal) : term4 x.
Proof. exact (ex_intro (term6 x) x (@lem1338000 x)). Qed.
Lemma lem1338002 (x : prod hreal hreal) : (term5 x) = (treal_eq x).
Proof. exact (EQ_MP (@lem1337999 x) (@lem1338001 x)). Qed.
Lemma lem1338003 (x : prod hreal hreal) : (term7 x) = (term8 x).
Proof. exact (@lem1337998 (term9 x)). Qed.
Lemma lem1338004 (x : prod hreal hreal) : (term5 x) = (treal_eq x).
Proof. exact (@lem1338002 x). Qed.
Lemma lem1338005 (x : prod hreal hreal) : (term10 x) = (term10 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1338006 (x : prod hreal hreal) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem1338005 x) (@lem1338004 x)). Qed.
Lemma lem1338007 (x : prod hreal hreal) : (term12 x) = ((term7 x) = (term13 x)).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1338008 (x : prod hreal hreal) : (term14 x) = (term14 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1338009 (x : prod hreal hreal) : ((term11 x) = (term12 x)) = ((term11 x) = ((term7 x) = (term13 x))).
Proof. exact (MK_COMB (@lem1338008 x) (@lem1338007 x)). Qed.
Lemma lem1338010 (x : prod hreal hreal) : (term11 x) = ((term7 x) = (term8 x)).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1338011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1338012 (x : prod hreal hreal) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem1338011) (@lem1338010 x)). Qed.
Lemma lem1338013 (x : prod hreal hreal) : ((term7 x) = (term13 x)) = ((term7 x) = (term13 x)).
Proof. exact (eq_refl ((term7 x) = (term13 x))). Qed.
Lemma lem1338014 (x : prod hreal hreal) : ((term11 x) = ((term7 x) = (term13 x))) = (((term7 x) = (term8 x)) = ((term7 x) = (term13 x))).
Proof. exact (MK_COMB (@lem1338012 x) (@lem1338013 x)). Qed.
Lemma lem1338015 (x : prod hreal hreal) : ((term11 x) = (term12 x)) = (((term7 x) = (term8 x)) = ((term7 x) = (term13 x))).
Proof. exact (TRANS (@lem1338009 x) (@lem1338014 x)). Qed.
Lemma lem1338016 (x : prod hreal hreal) : ((term7 x) = (term8 x)) = ((term7 x) = (term13 x)).
Proof. exact (EQ_MP (@lem1338015 x) (@lem1338006 x)). Qed.
Lemma lem1338017 (x : prod hreal hreal) : (term7 x) = (term13 x).
Proof. exact (EQ_MP (@lem1338016 x) (@lem1338003 x)). Qed.
Lemma lem1338018 (u : prod hreal hreal) (x : prod hreal hreal) (x' : prod hreal hreal) (h1 : term16 u x x') : term16 u x x'.
Proof. exact (h1). Qed.
Lemma lem1338019 (u : prod hreal hreal) (x : prod hreal hreal) (x' : prod hreal hreal) (h1 : term16 u x x') : treal_eq x x'.
Proof. exact (proj2 (@lem1338018 u x x' h1)). Qed.
Lemma lem1338020 (u : prod hreal hreal) (x : prod hreal hreal) (x' : prod hreal hreal) (h1 : term16 u x x') : term17 x' u.
Proof. exact (proj1 (@lem1338018 u x x' h1)). Qed.
Lemma lem1338021 (x : prod hreal hreal) : term18 x.
Proof. exact (@lem1337478 x). Qed.
Lemma lem1338022 (x : prod hreal hreal) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1338023 (x : prod hreal hreal) : term19 x.
Proof. exact (EQ_MP (@lem1338022 x) (@lem1338021 x)). Qed.
Lemma lem1338024 (x : prod hreal hreal) (y : prod hreal hreal) : term20 x y.
Proof. exact (@lem1338023 x y). Qed.
Lemma lem1338025 (x : prod hreal hreal) (y : prod hreal hreal) : (term20 x y) = (term21 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1338028 (x : prod hreal hreal) (y : prod hreal hreal) : term21 x y.
Proof. exact (EQ_MP (@lem1338025 x y) (@lem1338024 x y)). Qed.
Lemma lem1338029 (x : prod hreal hreal) (x' : prod hreal hreal) : term21 x x'.
Proof. exact (@lem1338028 x x'). Qed.
Lemma lem1338030 (u : prod hreal hreal) (x : prod hreal hreal) (x' : prod hreal hreal) (h1 : term16 u x x') : term22 x x'.
Proof. exact (@lem1338029 x x' (@lem1338019 u x x' h1)). Qed.
Lemma lem1338031 (u : prod hreal hreal) (x : prod hreal hreal) (x' : prod hreal hreal) (h1 : term16 u x x') : term23 x x' u.
Proof. exact (conj (@lem1338030 u x x' h1) (@lem1338020 u x x' h1)). Qed.
Lemma lem1338032 (x : prod hreal hreal) : term24 x.
Proof. exact (@lem1326778 x). Qed.
Lemma lem1338033 (x : prod hreal hreal) : (term24 x) = (term25 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1338034 (x : prod hreal hreal) : term25 x.
Proof. exact (EQ_MP (@lem1338033 x) (@lem1338032 x)). Qed.
Lemma lem1338035 (x : prod hreal hreal) (y : prod hreal hreal) : term26 x y.
Proof. exact (@lem1338034 x y). Qed.
Lemma lem1338036 (y : prod hreal hreal) (x : prod hreal hreal) : (term26 x y) = (term27 y x).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1338037 (y : prod hreal hreal) (x : prod hreal hreal) : term27 y x.
Proof. exact (EQ_MP (@lem1338036 y x) (@lem1338035 x y)). Qed.
Lemma lem1338038 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : term28 y x z.
Proof. exact (@lem1338037 y x z). Qed.
Lemma lem1338039 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term28 y x z) = (term29 y x z).
Proof. exact (eq_refl (term28 y x z)). Qed.
Lemma lem1338042 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : term29 y x z.
Proof. exact (EQ_MP (@lem1338039 y x z) (@lem1338038 y x z)). Qed.
Lemma lem1338043 (x' : prod hreal hreal) (x : prod hreal hreal) (u : prod hreal hreal) : term30 x' x u.
Proof. exact (@lem1338042 (treal_inv x') (treal_inv x) u). Qed.
Lemma lem1338044 (u : prod hreal hreal) (x : prod hreal hreal) (x' : prod hreal hreal) (h1 : term16 u x x') : term17 x u.
Proof. exact (@lem1338043 x' x u (@lem1338031 u x x' h1)). Qed.
Lemma lem1338045 (u : prod hreal hreal) (x : prod hreal hreal) (h1 : term31 u x) : term31 u x.
Proof. exact (h1). Qed.
Lemma lem1338046 (u : prod hreal hreal) (x : prod hreal hreal) (h1 : term31 u x) : term17 x u.
Proof. exact (ex_elim (@lem1338045 u x h1) (fun x' : prod hreal hreal => fun h0 : term32 u x x' => @lem1338044 u x x' h0)). Qed.
Lemma lem1338047 (x : prod hreal hreal) (u : prod hreal hreal) (h1 : term17 x u) : term17 x u.
Proof. exact (h1). Qed.
Lemma lem1338048 (x : prod hreal hreal) : term33 x.
Proof. exact (@lem1326193 x). Qed.
Lemma lem1338049 (x : prod hreal hreal) : (term33 x) = (treal_eq x x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1338050 (x : prod hreal hreal) : treal_eq x x.
Proof. exact (EQ_MP (@lem1338049 x) (@lem1338048 x)). Qed.
Lemma lem1338051 (x : prod hreal hreal) (u : prod hreal hreal) (h1 : term17 x u) : term34 u x.
Proof. exact (conj (@lem1338047 x u h1) (@lem1338050 x)). Qed.
Lemma lem1338052 (u : prod hreal hreal) (x : prod hreal hreal) (x' : prod hreal hreal) (h1 : term16 u x x') : term16 u x x'.
Proof. exact (h1). Qed.
Lemma lem1338053 (u : prod hreal hreal) (x : prod hreal hreal) (x' : prod hreal hreal) (h1 : term16 u x x') : term31 u x.
Proof. exact (ex_intro (term32 u x) x' (@lem1338052 u x x' h1)). Qed.
Lemma lem1338056 (x' : prod hreal hreal) (u : prod hreal hreal) (x : prod hreal hreal) : term35 x' u x.
Proof. exact (fun h0 : term16 u x x' => @lem1338053 u x x' h0). Qed.
Lemma lem1338057 (u : prod hreal hreal) (x : prod hreal hreal) : term36 u x.
Proof. exact (@lem1338056 x u x). Qed.
Lemma lem1338058 (x : prod hreal hreal) (u : prod hreal hreal) (h1 : term17 x u) : term31 u x.
Proof. exact (@lem1338057 u x (@lem1338051 x u h1)). Qed.
Lemma lem1338059 (u : prod hreal hreal) (x : prod hreal hreal) : term37 u x.
Proof. exact (fun h0 : term17 x u => @lem1338058 x u h0). Qed.
Lemma lem1338060 (x : prod hreal hreal) (u : prod hreal hreal) : term38 x u.
Proof. exact (fun h0 : term31 u x => @lem1338046 u x h0). Qed.
Lemma lem1338061 (u : prod hreal hreal) (x : prod hreal hreal) : term39 u x.
Proof. exact (conj (@lem1338060 x u) (@lem1338059 u x)). Qed.
Lemma lem1338062 (x : prod hreal hreal) (u : prod hreal hreal) : (term39 u x) = ((term31 u x) = (term17 x u)).
Proof. exact (@lem32 (term31 u x) (term17 x u)). Qed.
Lemma lem1338063 (x : prod hreal hreal) (u : prod hreal hreal) : (term31 u x) = (term17 x u).
Proof. exact (EQ_MP (@lem1338062 x u) (@lem1338061 u x)). Qed.
Lemma lem1338064 (x : prod hreal hreal) : (term40 x) = (term41 x).
Proof. exact (fun_ext (fun u : prod hreal hreal => @lem1338063 x u)). Qed.
Lemma lem1338065 : mk_real = mk_real.
Proof. exact (eq_refl mk_real). Qed.
Lemma lem1338066 (x : prod hreal hreal) : (term13 x) = (term42 x).
Proof. exact (MK_COMB (@lem1338065) (@lem1338064 x)). Qed.
Lemma lem1338067 (x : prod hreal hreal) : (term7 x) = (term42 x).
Proof. exact (TRANS (@lem1338017 x) (@lem1338066 x)). Qed.
Lemma lem1338068 (t : type1233) : (term43 t) = t.
Proof. exact (@lem9127 (prod hreal hreal) Prop t). Qed.
Lemma lem1338071 (x : prod hreal hreal) : (term41 x) = (term44 x).
Proof. exact (@lem1338068 (term44 x)). Qed.
Lemma lem1338072 : mk_real = mk_real.
Proof. exact (eq_refl mk_real). Qed.
Lemma lem1338073 (x : prod hreal hreal) : (term42 x) = (term45 x).
Proof. exact (MK_COMB (@lem1338072) (@lem1338071 x)). Qed.
Lemma lem1338074 (x : prod hreal hreal) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1338075 (x : prod hreal hreal) : ((term7 x) = (term42 x)) = ((term7 x) = (term45 x)).
Proof. exact (MK_COMB (@lem1338074 x) (@lem1338073 x)). Qed.
Lemma lem1338076 (x : prod hreal hreal) : (term7 x) = (term45 x).
Proof. exact (EQ_MP (@lem1338075 x) (@lem1338067 x)). Qed.
