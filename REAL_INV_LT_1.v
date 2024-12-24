Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_LT_1_term_abbrevs.
Require Import REAL_INV_1_spec.
Require Import REAL_LT_01_spec.
Require Import REAL_LT_INV2_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1633037 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1633038 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1633037 h1 x). Qed.
Lemma lem1633039 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1633040 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1633039 x) (@lem1633038 x h1)). Qed.
Lemma lem1633041 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1633040 x h1 y). Qed.
Lemma lem1633042 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1633043 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1633042 y x) (@lem1633041 x y h1)). Qed.
Lemma lem1633044 (x : real) (y : real) (h1 : term5 x y) : term5 x y.
Proof. exact (h1). Qed.
Lemma lem1633045 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 y x.
Proof. exact (@lem1633043 y x h1 (@lem1633044 x y h2)). Qed.
Lemma lem1633046 (x : real) (y : real) (h1 : term5 x y) : term7 y x.
Proof. exact (fun h0 : term0 => @lem1633045 x y h0 h1). Qed.
Lemma lem1633047 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1633048 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 y x.
Proof. exact (@lem1633046 x y h2 (@lem1633047 h1)). Qed.
Lemma lem1633049 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (fun h0 : term5 x y => @lem1633048 x y h1 h0). Qed.
Lemma lem1633050 (y : real) (h1 : term0) : term8 y.
Proof. exact (fun x : real => @lem1633049 y x h1). Qed.
Lemma lem1633051 (h1 : term0) : term9.
Proof. exact (fun y : real => @lem1633050 y h1). Qed.
Lemma lem1633052 : term10.
Proof. exact (fun h0 : term0 => @lem1633051 h0). Qed.
Lemma lem1633053 : term9.
Proof. exact (@lem1633052 (@lem1632194)). Qed.
Lemma lem1633054 (y : real) : term11 y.
Proof. exact (@lem1633053 y). Qed.
Lemma lem1633055 (y : real) : (term11 y) = (term8 y).
Proof. exact (eq_refl (term11 y)). Qed.
Lemma lem1633056 (y : real) : term8 y.
Proof. exact (EQ_MP (@lem1633055 y) (@lem1633054 y)). Qed.
Lemma lem1633057 (y : real) (x : real) : term12 y x.
Proof. exact (@lem1633056 y x). Qed.
Lemma lem1633058 (y : real) (x : real) : (term12 y x) = (term4 y x).
Proof. exact (eq_refl (term12 y x)). Qed.
Lemma lem1633060 (h1 : term13 = term14) : term13 = term14.
Proof. exact (h1). Qed.
Lemma lem1633061 (h1 : term13 = term14) : term14 = term13.
Proof. exact (SYM (@lem1633060 h1)). Qed.
Lemma lem1633062 (h1 : term14 = term13) : term14 = term13.
Proof. exact (h1). Qed.
Lemma lem1633063 (h1 : term14 = term13) : term13 = term14.
Proof. exact (SYM (@lem1633062 h1)). Qed.
Lemma lem1633064 : (term13 = term14) = (term14 = term13).
Proof. exact (prop_ext (fun h1 : term13 = term14 => @lem1633061 h1) (fun h1 : term14 = term13 => @lem1633063 h1)). Qed.
Lemma lem1633066 (x : real) (h1 : term15 x) : term15 x.
Proof. exact (h1). Qed.
Lemma lem1633068 : term14 = term13.
Proof. exact (EQ_MP (@lem1633064) (@lem1592031)). Qed.
Lemma lem1633069 (x : real) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1633070 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1633069 x) (@lem1633068)). Qed.
Lemma lem1633071 (x : real) : (term18 x) = (term17 x).
Proof. exact (SYM (@lem1633070 x)). Qed.
Lemma lem1633073 (y : real) (x : real) : term4 y x.
Proof. exact (EQ_MP (@lem1633058 y x) (@lem1633057 y x)). Qed.
Lemma lem1633074 (x : real) : term19 x.
Proof. exact (@lem1633073 x term14). Qed.
Lemma lem1633075 : term20 = (term20 = True).
Proof. exact (@lem7 term20). Qed.
Lemma lem1633077 (x : real) : (term15 x) = ((term15 x) = True).
Proof. exact (@lem7 (term15 x)). Qed.
Lemma lem1633082 : term20 = True.
Proof. exact (EQ_MP (@lem1633075) (@lem1499399)). Qed.
Lemma lem1633083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1633084 : term21 = (and True).
Proof. exact (MK_COMB (@lem1633083) (@lem1633082)). Qed.
Lemma lem1633086 (x : real) (h1 : term15 x) : (term15 x) = True.
Proof. exact (EQ_MP (@lem1633077 x) (@lem1633066 x h1)). Qed.
Lemma lem1633087 (x : real) (h1 : term15 x) : (term22 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1633084) (@lem1633086 x h1)). Qed.
Lemma lem1633089 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1633090 : (True /\ True) = True.
Proof. exact (@lem1633089 True). Qed.
Lemma lem1633091 (x : real) (h1 : term15 x) : (term22 x) = True.
Proof. exact (TRANS (@lem1633087 x h1) (@lem1633090)). Qed.
Lemma lem1633092 (x : real) (h1 : term15 x) : True = (term22 x).
Proof. exact (SYM (@lem1633091 x h1)). Qed.
Lemma lem1633093 (x : real) (h1 : term15 x) : term22 x.
Proof. exact (EQ_MP (@lem1633092 x h1) (@lem0)). Qed.
Lemma lem1633094 (x : real) (h1 : term15 x) : term18 x.
Proof. exact (@lem1633074 x (@lem1633093 x h1)). Qed.
Lemma lem1633095 (x : real) (h1 : term15 x) : term17 x.
Proof. exact (EQ_MP (@lem1633071 x) (@lem1633094 x h1)). Qed.
Lemma lem1633096 (x : real) (h1 : term15 x) : (term15 x) = (term17 x).
Proof. exact (prop_ext (fun h2 : term15 x => @lem1633095 x h1) (fun h2 : term17 x => @lem1633066 x h1)). Qed.
Lemma lem1633097 (x : real) (h1 : term15 x) : term17 x.
Proof. exact (EQ_MP (@lem1633096 x h1) (@lem1633066 x h1)). Qed.
Lemma lem1633098 (x : real) : term23 x.
Proof. exact (fun h0 : term15 x => @lem1633097 x h0). Qed.
Lemma lem1633103 : term24.
Proof. exact (fun x : real => @lem1633098 x). Qed.
