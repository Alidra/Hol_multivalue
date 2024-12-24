Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_ADD_LCANCEL_term_abbrevs.
Require Import thm0_spec.
Require Import thm1338438_spec.
Require Import thm1338512_spec.
Require Import thm1338588_spec.
Require Import thm1823_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Lemma lem1353038 (x : real) : term0 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1353039 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1353041 (x : real) : term2 x.
Proof. exact (@lem1338588 x). Qed.
Lemma lem1353042 (x : real) : (term2 x) = ((term3 x) = term4).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1353044 (x : real) : term5 x.
Proof. exact (@lem1338438 x). Qed.
Lemma lem1353045 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1353046 (x : real) : term6 x.
Proof. exact (EQ_MP (@lem1353045 x) (@lem1353044 x)). Qed.
Lemma lem1353047 (x : real) (y : real) : term7 x y.
Proof. exact (@lem1353046 x y). Qed.
Lemma lem1353048 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1353049 (x : real) (y : real) : term8 x y.
Proof. exact (EQ_MP (@lem1353048 x y) (@lem1353047 x y)). Qed.
Lemma lem1353050 (x : real) (y : real) (z : real) : term9 x y z.
Proof. exact (@lem1353049 x y z). Qed.
Lemma lem1353051 (x : real) (y : real) (z : real) : (term9 x y z) = ((term10 x y z) = (term11 x y z)).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1353053 (x : real) : (term12 x) = (term12 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1353054 (y : real) (x : real) (z : real) (h1 : (real_add x y) = (real_add x z)) : (real_add x y) = (real_add x z).
Proof. exact (h1). Qed.
Lemma lem1353063 (y : real) (z : real) (h1 : y = z) : y = z.
Proof. exact (h1). Qed.
Lemma lem1353064 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1353065 (x : real) (y : real) (z : real) (h1 : y = z) : (real_add x y) = (real_add x z).
Proof. exact (MK_COMB (@lem1353064 x) (@lem1353063 y z h1)). Qed.
Lemma lem1353066 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1353067 (x : real) (y : real) (z : real) (h1 : y = z) : (term13 x y) = (term13 x z).
Proof. exact (MK_COMB (@lem1353066) (@lem1353065 x y z h1)). Qed.
Lemma lem1353068 (x : real) (z : real) : (real_add x z) = (real_add x z).
Proof. exact (eq_refl (real_add x z)). Qed.
Lemma lem1353069 (x : real) (y : real) (z : real) (h1 : y = z) : ((real_add x y) = (real_add x z)) = ((real_add x z) = (real_add x z)).
Proof. exact (MK_COMB (@lem1353067 x y z h1) (@lem1353068 x z)). Qed.
Lemma lem1353071 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1353072 (x : real) : (x = x) = True.
Proof. exact (@lem1353071 real x). Qed.
Lemma lem1353073 (x : real) (z : real) : ((real_add x z) = (real_add x z)) = True.
Proof. exact (@lem1353072 (real_add x z)). Qed.
Lemma lem1353074 (x : real) (y : real) (z : real) (h1 : y = z) : ((real_add x y) = (real_add x z)) = True.
Proof. exact (TRANS (@lem1353069 x y z h1) (@lem1353073 x z)). Qed.
Lemma lem1353075 (x : real) (y : real) (z : real) (h1 : y = z) : True = ((real_add x y) = (real_add x z)).
Proof. exact (SYM (@lem1353074 x y z h1)). Qed.
Lemma lem1353076 (x : real) (y : real) (z : real) (h1 : y = z) : (real_add x y) = (real_add x z).
Proof. exact (EQ_MP (@lem1353075 x y z h1) (@lem0)). Qed.
Lemma lem1353077 (y : real) (x : real) (z : real) (h1 : (real_add x y) = (real_add x z)) : (term14 x y) = (term14 x z).
Proof. exact (MK_COMB (@lem1353053 x) (@lem1353054 y x z h1)). Qed.
Lemma lem1353087 (x : real) (y : real) (z : real) : (term10 x y z) = (term11 x y z).
Proof. exact (EQ_MP (@lem1353051 x y z) (@lem1353050 x y z)). Qed.
Lemma lem1353088 (x : real) (y : real) : (term14 x y) = (term15 x y).
Proof. exact (@lem1353087 (real_neg x) x y). Qed.
Lemma lem1353090 (x : real) : (term3 x) = term4.
Proof. exact (EQ_MP (@lem1353042 x) (@lem1353041 x)). Qed.
Lemma lem1353091 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1353092 (x : real) : (term16 x) = term17.
Proof. exact (MK_COMB (@lem1353091) (@lem1353090 x)). Qed.
Lemma lem1353093 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1353094 (x : real) (y : real) : (term15 x y) = (term1 y).
Proof. exact (MK_COMB (@lem1353092 x) (@lem1353093 y)). Qed.
Lemma lem1353096 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1353039 x) (@lem1353038 x)). Qed.
Lemma lem1353097 (y : real) : (term1 y) = y.
Proof. exact (@lem1353096 y). Qed.
Lemma lem1353098 (x : real) (y : real) : (term15 x y) = y.
Proof. exact (TRANS (@lem1353094 x y) (@lem1353097 y)). Qed.
Lemma lem1353099 (x : real) (y : real) : (term14 x y) = y.
Proof. exact (TRANS (@lem1353088 x y) (@lem1353098 x y)). Qed.
Lemma lem1353100 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1353101 (x : real) (y : real) : (term18 x y) = (@eq real y).
Proof. exact (MK_COMB (@lem1353100) (@lem1353099 x y)). Qed.
Lemma lem1353105 (x : real) (y : real) (z : real) : (term10 x y z) = (term11 x y z).
Proof. exact (EQ_MP (@lem1353051 x y z) (@lem1353050 x y z)). Qed.
Lemma lem1353106 (x : real) (z : real) : (term14 x z) = (term15 x z).
Proof. exact (@lem1353105 (real_neg x) x z). Qed.
Lemma lem1353108 (x : real) : (term3 x) = term4.
Proof. exact (EQ_MP (@lem1353042 x) (@lem1353041 x)). Qed.
Lemma lem1353109 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1353110 (x : real) : (term16 x) = term17.
Proof. exact (MK_COMB (@lem1353109) (@lem1353108 x)). Qed.
Lemma lem1353111 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1353112 (x : real) (z : real) : (term15 x z) = (term1 z).
Proof. exact (MK_COMB (@lem1353110 x) (@lem1353111 z)). Qed.
Lemma lem1353114 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1353039 x) (@lem1353038 x)). Qed.
Lemma lem1353115 (z : real) : (term1 z) = z.
Proof. exact (@lem1353114 z). Qed.
Lemma lem1353116 (x : real) (z : real) : (term15 x z) = z.
Proof. exact (TRANS (@lem1353112 x z) (@lem1353115 z)). Qed.
Lemma lem1353117 (x : real) (z : real) : (term14 x z) = z.
Proof. exact (TRANS (@lem1353106 x z) (@lem1353116 x z)). Qed.
Lemma lem1353118 (x : real) (y : real) (z : real) : ((term14 x y) = (term14 x z)) = (y = z).
Proof. exact (MK_COMB (@lem1353101 x y) (@lem1353117 x z)). Qed.
Lemma lem1353121 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1353122 (x : real) (y : real) (z : real) : (term19 y x z) = (term20 y z).
Proof. exact (MK_COMB (@lem1353121) (@lem1353118 x y z)). Qed.
Lemma lem1353125 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1353126 (x : real) (y : real) (z : real) : (term21 x y z) = (term22 y z).
Proof. exact (MK_COMB (@lem1353122 x y z) (@lem1353125 y z)). Qed.
Lemma lem1353130 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1353131 (y : real) (z : real) : (term22 y z) = True.
Proof. exact (@lem1353130 (y = z)). Qed.
Lemma lem1353132 (x : real) (y : real) (z : real) : (term21 x y z) = True.
Proof. exact (TRANS (@lem1353126 x y z) (@lem1353131 y z)). Qed.
Lemma lem1353133 (x : real) (y : real) (z : real) : True = (term21 x y z).
Proof. exact (SYM (@lem1353132 x y z)). Qed.
Lemma lem1353134 (x : real) (y : real) (z : real) : term21 x y z.
Proof. exact (EQ_MP (@lem1353133 x y z) (@lem0)). Qed.
Lemma lem1353136 (y : real) (x : real) (z : real) (h1 : (real_add x y) = (real_add x z)) : y = z.
Proof. exact (@lem1353134 x y z (@lem1353077 y x z h1)). Qed.
Lemma lem1353137 (y : real) (x : real) (z : real) : term23 y x z.
Proof. exact (fun h0 : y = z => @lem1353076 x y z h0). Qed.
Lemma lem1353138 (x : real) (y : real) (z : real) : term24 x y z.
Proof. exact (fun h0 : (real_add x y) = (real_add x z) => @lem1353136 y x z h0). Qed.
Lemma lem1353139 (y : real) (x : real) (z : real) : term25 y x z.
Proof. exact (conj (@lem1353138 x y z) (@lem1353137 y x z)). Qed.
Lemma lem1353140 (x : real) (y : real) (z : real) : (term25 y x z) = (((real_add x y) = (real_add x z)) = (y = z)).
Proof. exact (@lem32 ((real_add x y) = (real_add x z)) (y = z)). Qed.
Lemma lem1353141 (x : real) (y : real) (z : real) : ((real_add x y) = (real_add x z)) = (y = z).
Proof. exact (EQ_MP (@lem1353140 x y z) (@lem1353139 y x z)). Qed.
Lemma lem1353146 (x : real) (y : real) : term26 x y.
Proof. exact (fun z : real => @lem1353141 x y z). Qed.
Lemma lem1353151 (x : real) : term27 x.
Proof. exact (fun y : real => @lem1353146 x y). Qed.
Lemma lem1353156 : term28.
Proof. exact (fun x : real => @lem1353151 x). Qed.
