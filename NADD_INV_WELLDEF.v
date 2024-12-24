Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_INV_WELLDEF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_EQ_SYM_spec.
Require Import NADD_EQ_TRANS_spec.
Require Import NADD_MUL_ASSOC_spec.
Require Import NADD_MUL_LID_spec.
Require Import NADD_MUL_LINV_spec.
Require Import NADD_MUL_SYM_spec.
Require Import NADD_MUL_WELLDEF_spec.
Require Import nadd_inv_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem1309023 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1309024 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1309025 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1309024 t1) (@lem1309023 t1)). Qed.
Lemma lem1309026 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1309025 t1 t2). Qed.
Lemma lem1309027 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1309028 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1309027 t1 t2) (@lem1309026 t1 t2)). Qed.
Lemma lem1309029 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1309028 t1 t2 t3). Qed.
Lemma lem1309030 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1309031 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1309030 t1 t2 t3) (@lem1309029 t1 t2 t3)). Qed.
Lemma lem1309032 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1309031 t1 t2 t3)). Qed.
Lemma lem1309033 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1309034 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1309035 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1309034 t1) (@lem1309033 t1)). Qed.
Lemma lem1309036 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1309035 t1 t2). Qed.
Lemma lem1309037 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1309038 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1309037 t1 t2) (@lem1309036 t1 t2)). Qed.
Lemma lem1309039 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1309038 t1 t2 t3). Qed.
Lemma lem1309040 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1309041 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1309040 t1 t2 t3) (@lem1309039 t1 t2 t3)). Qed.
Lemma lem1309042 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1309041 t1 t2 t3)). Qed.
Lemma lem1309043 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1309044 (x : nadd) (h1 : term7) : term8 x.
Proof. exact (@lem1309043 h1 x). Qed.
Lemma lem1309045 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1309046 (x : nadd) (h1 : term7) : term9 x.
Proof. exact (EQ_MP (@lem1309045 x) (@lem1309044 x h1)). Qed.
Lemma lem1309047 (x : nadd) (y : nadd) (h1 : term7) : term10 x y.
Proof. exact (@lem1309046 x h1 y). Qed.
Lemma lem1309048 (y : nadd) (x : nadd) : (term10 x y) = (term11 y x).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1309049 (y : nadd) (x : nadd) (h1 : term7) : term11 y x.
Proof. exact (EQ_MP (@lem1309048 y x) (@lem1309047 x y h1)). Qed.
Lemma lem1309050 (y : nadd) (x : nadd) (z : nadd) (h1 : term7) : term12 y x z.
Proof. exact (@lem1309049 y x h1 z). Qed.
Lemma lem1309051 (y : nadd) (x : nadd) (z : nadd) : (term12 y x z) = (term13 y x z).
Proof. exact (eq_refl (term12 y x z)). Qed.
Lemma lem1309052 (y : nadd) (x : nadd) (z : nadd) (h1 : term7) : term13 y x z.
Proof. exact (EQ_MP (@lem1309051 y x z) (@lem1309050 y x z h1)). Qed.
Lemma lem1309053 (x : nadd) (y : nadd) (z : nadd) (h1 : term14 x y z) : term14 x y z.
Proof. exact (h1). Qed.
Lemma lem1309054 (x : nadd) (y : nadd) (z : nadd) (h1 : term7) (h2 : term14 x y z) : nadd_eq x z.
Proof. exact (@lem1309052 y x z h1 (@lem1309053 x y z h2)). Qed.
Lemma lem1309055 (x : nadd) (y : nadd) (z : nadd) (h1 : term14 x y z) : term15 x z.
Proof. exact (fun h0 : term7 => @lem1309054 x y z h0 h1). Qed.
Lemma lem1309056 (x : nadd) (z : nadd) (h1 : term16 x z) : term16 x z.
Proof. exact (h1). Qed.
Lemma lem1309057 (x : nadd) (z : nadd) (h1 : term16 x z) : term15 x z.
Proof. exact (ex_elim (@lem1309056 x z h1) (fun y : nadd => fun h0 : term17 x z y => @lem1309055 x y z h0)). Qed.
Lemma lem1309058 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1309059 (x : nadd) (z : nadd) (h1 : term7) (h2 : term16 x z) : nadd_eq x z.
Proof. exact (@lem1309057 x z h2 (@lem1309058 h1)). Qed.
Lemma lem1309060 (x : nadd) (z : nadd) (h1 : term7) : term18 x z.
Proof. exact (fun h0 : term16 x z => @lem1309059 x z h1 h0). Qed.
Lemma lem1309061 (x : nadd) (h1 : term7) : term19 x.
Proof. exact (fun z : nadd => @lem1309060 x z h1). Qed.
Lemma lem1309062 (h1 : term7) : term20.
Proof. exact (fun x : nadd => @lem1309061 x h1). Qed.
Lemma lem1309063 : term21.
Proof. exact (fun h0 : term7 => @lem1309062 h0). Qed.
Lemma lem1309064 : term20.
Proof. exact (@lem1309063 (@lem1268295)). Qed.
Lemma lem1309065 (x : nadd) : term22 x.
Proof. exact (@lem1309064 x). Qed.
Lemma lem1309066 (x : nadd) : (term22 x) = (term19 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1309067 (x : nadd) : term19 x.
Proof. exact (EQ_MP (@lem1309066 x) (@lem1309065 x)). Qed.
Lemma lem1309068 (x : nadd) (z : nadd) : term23 x z.
Proof. exact (@lem1309067 x z). Qed.
Lemma lem1309069 (x : nadd) (z : nadd) : (term23 x z) = (term18 x z).
Proof. exact (eq_refl (term23 x z)). Qed.
Lemma lem1309071 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1309072 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1309073 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1309072 t1) (@lem1309071 t1)). Qed.
Lemma lem1309074 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1309073 t1 t2). Qed.
Lemma lem1309075 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1309076 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1309075 t1 t2) (@lem1309074 t1 t2)). Qed.
Lemma lem1309077 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1309076 t1 t2 t3). Qed.
Lemma lem1309078 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1309079 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1309078 t1 t2 t3) (@lem1309077 t1 t2 t3)). Qed.
Lemma lem1309080 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1309079 t1 t2 t3)). Qed.
Lemma lem1309081 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1309082 (x : nadd) (h1 : term7) : term8 x.
Proof. exact (@lem1309081 h1 x). Qed.
Lemma lem1309083 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1309084 (x : nadd) (h1 : term7) : term9 x.
Proof. exact (EQ_MP (@lem1309083 x) (@lem1309082 x h1)). Qed.
Lemma lem1309085 (x : nadd) (y : nadd) (h1 : term7) : term10 x y.
Proof. exact (@lem1309084 x h1 y). Qed.
Lemma lem1309086 (y : nadd) (x : nadd) : (term10 x y) = (term11 y x).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1309087 (y : nadd) (x : nadd) (h1 : term7) : term11 y x.
Proof. exact (EQ_MP (@lem1309086 y x) (@lem1309085 x y h1)). Qed.
Lemma lem1309088 (y : nadd) (x : nadd) (z : nadd) (h1 : term7) : term12 y x z.
Proof. exact (@lem1309087 y x h1 z). Qed.
Lemma lem1309089 (y : nadd) (x : nadd) (z : nadd) : (term12 y x z) = (term13 y x z).
Proof. exact (eq_refl (term12 y x z)). Qed.
Lemma lem1309090 (y : nadd) (x : nadd) (z : nadd) (h1 : term7) : term13 y x z.
Proof. exact (EQ_MP (@lem1309089 y x z) (@lem1309088 y x z h1)). Qed.
Lemma lem1309091 (x : nadd) (y : nadd) (z : nadd) (h1 : term14 x y z) : term14 x y z.
Proof. exact (h1). Qed.
Lemma lem1309092 (x : nadd) (y : nadd) (z : nadd) (h1 : term7) (h2 : term14 x y z) : nadd_eq x z.
Proof. exact (@lem1309090 y x z h1 (@lem1309091 x y z h2)). Qed.
Lemma lem1309093 (x : nadd) (y : nadd) (z : nadd) (h1 : term14 x y z) : term15 x z.
Proof. exact (fun h0 : term7 => @lem1309092 x y z h0 h1). Qed.
Lemma lem1309094 (x : nadd) (z : nadd) (h1 : term16 x z) : term16 x z.
Proof. exact (h1). Qed.
Lemma lem1309095 (x : nadd) (z : nadd) (h1 : term16 x z) : term15 x z.
Proof. exact (ex_elim (@lem1309094 x z h1) (fun y : nadd => fun h0 : term17 x z y => @lem1309093 x y z h0)). Qed.
Lemma lem1309096 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1309097 (x : nadd) (z : nadd) (h1 : term7) (h2 : term16 x z) : nadd_eq x z.
Proof. exact (@lem1309095 x z h2 (@lem1309096 h1)). Qed.
Lemma lem1309098 (x : nadd) (z : nadd) (h1 : term7) : term18 x z.
Proof. exact (fun h0 : term16 x z => @lem1309097 x z h1 h0). Qed.
Lemma lem1309099 (x : nadd) (h1 : term7) : term19 x.
Proof. exact (fun z : nadd => @lem1309098 x z h1). Qed.
Lemma lem1309100 (h1 : term7) : term20.
Proof. exact (fun x : nadd => @lem1309099 x h1). Qed.
Lemma lem1309101 : term21.
Proof. exact (fun h0 : term7 => @lem1309100 h0). Qed.
Lemma lem1309102 : term20.
Proof. exact (@lem1309101 (@lem1268295)). Qed.
Lemma lem1309103 (x : nadd) : term22 x.
Proof. exact (@lem1309102 x). Qed.
Lemma lem1309104 (x : nadd) : (term22 x) = (term19 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1309105 (x : nadd) : term19 x.
Proof. exact (EQ_MP (@lem1309104 x) (@lem1309103 x)). Qed.
Lemma lem1309106 (x : nadd) (z : nadd) : term23 x z.
Proof. exact (@lem1309105 x z). Qed.
Lemma lem1309107 (x : nadd) (z : nadd) : (term23 x z) = (term18 x z).
Proof. exact (eq_refl (term23 x z)). Qed.
Lemma lem1309109 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1309110 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1309111 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1309110 t1) (@lem1309109 t1)). Qed.
Lemma lem1309112 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1309111 t1 t2). Qed.
Lemma lem1309113 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1309114 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1309113 t1 t2) (@lem1309112 t1 t2)). Qed.
Lemma lem1309115 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1309114 t1 t2 t3). Qed.
Lemma lem1309116 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1309117 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1309116 t1 t2 t3) (@lem1309115 t1 t2 t3)). Qed.
Lemma lem1309118 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1309117 t1 t2 t3)). Qed.
Lemma lem1309119 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1309120 (x : nadd) (h1 : term7) : term8 x.
Proof. exact (@lem1309119 h1 x). Qed.
Lemma lem1309121 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1309122 (x : nadd) (h1 : term7) : term9 x.
Proof. exact (EQ_MP (@lem1309121 x) (@lem1309120 x h1)). Qed.
Lemma lem1309123 (x : nadd) (y : nadd) (h1 : term7) : term10 x y.
Proof. exact (@lem1309122 x h1 y). Qed.
Lemma lem1309124 (y : nadd) (x : nadd) : (term10 x y) = (term11 y x).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1309125 (y : nadd) (x : nadd) (h1 : term7) : term11 y x.
Proof. exact (EQ_MP (@lem1309124 y x) (@lem1309123 x y h1)). Qed.
Lemma lem1309126 (y : nadd) (x : nadd) (z : nadd) (h1 : term7) : term12 y x z.
Proof. exact (@lem1309125 y x h1 z). Qed.
Lemma lem1309127 (y : nadd) (x : nadd) (z : nadd) : (term12 y x z) = (term13 y x z).
Proof. exact (eq_refl (term12 y x z)). Qed.
Lemma lem1309128 (y : nadd) (x : nadd) (z : nadd) (h1 : term7) : term13 y x z.
Proof. exact (EQ_MP (@lem1309127 y x z) (@lem1309126 y x z h1)). Qed.
Lemma lem1309129 (x : nadd) (y : nadd) (z : nadd) (h1 : term14 x y z) : term14 x y z.
Proof. exact (h1). Qed.
Lemma lem1309130 (x : nadd) (y : nadd) (z : nadd) (h1 : term7) (h2 : term14 x y z) : nadd_eq x z.
Proof. exact (@lem1309128 y x z h1 (@lem1309129 x y z h2)). Qed.
Lemma lem1309131 (x : nadd) (y : nadd) (z : nadd) (h1 : term14 x y z) : term15 x z.
Proof. exact (fun h0 : term7 => @lem1309130 x y z h0 h1). Qed.
Lemma lem1309132 (x : nadd) (z : nadd) (h1 : term16 x z) : term16 x z.
Proof. exact (h1). Qed.
Lemma lem1309133 (x : nadd) (z : nadd) (h1 : term16 x z) : term15 x z.
Proof. exact (ex_elim (@lem1309132 x z h1) (fun y : nadd => fun h0 : term17 x z y => @lem1309131 x y z h0)). Qed.
Lemma lem1309134 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1309135 (x : nadd) (z : nadd) (h1 : term7) (h2 : term16 x z) : nadd_eq x z.
Proof. exact (@lem1309133 x z h2 (@lem1309134 h1)). Qed.
Lemma lem1309136 (x : nadd) (z : nadd) (h1 : term7) : term18 x z.
Proof. exact (fun h0 : term16 x z => @lem1309135 x z h1 h0). Qed.
Lemma lem1309137 (x : nadd) (h1 : term7) : term19 x.
Proof. exact (fun z : nadd => @lem1309136 x z h1). Qed.
Lemma lem1309138 (h1 : term7) : term20.
Proof. exact (fun x : nadd => @lem1309137 x h1). Qed.
Lemma lem1309139 : term21.
Proof. exact (fun h0 : term7 => @lem1309138 h0). Qed.
Lemma lem1309140 : term20.
Proof. exact (@lem1309139 (@lem1268295)). Qed.
Lemma lem1309141 (x : nadd) : term22 x.
Proof. exact (@lem1309140 x). Qed.
Lemma lem1309142 (x : nadd) : (term22 x) = (term19 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1309143 (x : nadd) : term19 x.
Proof. exact (EQ_MP (@lem1309142 x) (@lem1309141 x)). Qed.
Lemma lem1309144 (x : nadd) (z : nadd) : term23 x z.
Proof. exact (@lem1309143 x z). Qed.
Lemma lem1309145 (x : nadd) (z : nadd) : (term23 x z) = (term18 x z).
Proof. exact (eq_refl (term23 x z)). Qed.
Lemma lem1309147 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1309148 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1309149 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1309148 t1) (@lem1309147 t1)). Qed.
Lemma lem1309150 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1309149 t1 t2). Qed.
Lemma lem1309151 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1309152 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1309151 t1 t2) (@lem1309150 t1 t2)). Qed.
Lemma lem1309153 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1309152 t1 t2 t3). Qed.
Lemma lem1309154 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1309155 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1309154 t1 t2 t3) (@lem1309153 t1 t2 t3)). Qed.
Lemma lem1309156 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1309155 t1 t2 t3)). Qed.
Lemma lem1309157 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1309158 (x : nadd) (h1 : term7) : term8 x.
Proof. exact (@lem1309157 h1 x). Qed.
Lemma lem1309159 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1309160 (x : nadd) (h1 : term7) : term9 x.
Proof. exact (EQ_MP (@lem1309159 x) (@lem1309158 x h1)). Qed.
Lemma lem1309161 (x : nadd) (y : nadd) (h1 : term7) : term10 x y.
Proof. exact (@lem1309160 x h1 y). Qed.
Lemma lem1309162 (y : nadd) (x : nadd) : (term10 x y) = (term11 y x).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1309163 (y : nadd) (x : nadd) (h1 : term7) : term11 y x.
Proof. exact (EQ_MP (@lem1309162 y x) (@lem1309161 x y h1)). Qed.
Lemma lem1309164 (y : nadd) (x : nadd) (z : nadd) (h1 : term7) : term12 y x z.
Proof. exact (@lem1309163 y x h1 z). Qed.
Lemma lem1309165 (y : nadd) (x : nadd) (z : nadd) : (term12 y x z) = (term13 y x z).
Proof. exact (eq_refl (term12 y x z)). Qed.
Lemma lem1309166 (y : nadd) (x : nadd) (z : nadd) (h1 : term7) : term13 y x z.
Proof. exact (EQ_MP (@lem1309165 y x z) (@lem1309164 y x z h1)). Qed.
Lemma lem1309167 (x : nadd) (y : nadd) (z : nadd) (h1 : term14 x y z) : term14 x y z.
Proof. exact (h1). Qed.
Lemma lem1309168 (x : nadd) (y : nadd) (z : nadd) (h1 : term7) (h2 : term14 x y z) : nadd_eq x z.
Proof. exact (@lem1309166 y x z h1 (@lem1309167 x y z h2)). Qed.
Lemma lem1309169 (x : nadd) (y : nadd) (z : nadd) (h1 : term14 x y z) : term15 x z.
Proof. exact (fun h0 : term7 => @lem1309168 x y z h0 h1). Qed.
Lemma lem1309170 (x : nadd) (z : nadd) (h1 : term16 x z) : term16 x z.
Proof. exact (h1). Qed.
Lemma lem1309171 (x : nadd) (z : nadd) (h1 : term16 x z) : term15 x z.
Proof. exact (ex_elim (@lem1309170 x z h1) (fun y : nadd => fun h0 : term17 x z y => @lem1309169 x y z h0)). Qed.
Lemma lem1309172 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1309173 (x : nadd) (z : nadd) (h1 : term7) (h2 : term16 x z) : nadd_eq x z.
Proof. exact (@lem1309171 x z h2 (@lem1309172 h1)). Qed.
Lemma lem1309174 (x : nadd) (z : nadd) (h1 : term7) : term18 x z.
Proof. exact (fun h0 : term16 x z => @lem1309173 x z h1 h0). Qed.
Lemma lem1309175 (x : nadd) (h1 : term7) : term19 x.
Proof. exact (fun z : nadd => @lem1309174 x z h1). Qed.
Lemma lem1309176 (h1 : term7) : term20.
Proof. exact (fun x : nadd => @lem1309175 x h1). Qed.
Lemma lem1309177 : term21.
Proof. exact (fun h0 : term7 => @lem1309176 h0). Qed.
Lemma lem1309178 : term20.
Proof. exact (@lem1309177 (@lem1268295)). Qed.
Lemma lem1309179 (x : nadd) : term22 x.
Proof. exact (@lem1309178 x). Qed.
Lemma lem1309180 (x : nadd) : (term22 x) = (term19 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1309181 (x : nadd) : term19 x.
Proof. exact (EQ_MP (@lem1309180 x) (@lem1309179 x)). Qed.
Lemma lem1309182 (x : nadd) (z : nadd) : term23 x z.
Proof. exact (@lem1309181 x z). Qed.
Lemma lem1309183 (x : nadd) (z : nadd) : (term23 x z) = (term18 x z).
Proof. exact (eq_refl (term23 x z)). Qed.
Lemma lem1309185 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1309186 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1309187 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1309186 t1) (@lem1309185 t1)). Qed.
Lemma lem1309188 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1309187 t1 t2). Qed.
Lemma lem1309189 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1309190 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1309189 t1 t2) (@lem1309188 t1 t2)). Qed.
Lemma lem1309191 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1309190 t1 t2 t3). Qed.
Lemma lem1309192 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1309193 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1309192 t1 t2 t3) (@lem1309191 t1 t2 t3)). Qed.
Lemma lem1309194 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1309193 t1 t2 t3)). Qed.
Lemma lem1309195 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1309196 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1309197 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1309196 t1) (@lem1309195 t1)). Qed.
Lemma lem1309198 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1309197 t1 t2). Qed.
Lemma lem1309199 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1309200 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1309199 t1 t2) (@lem1309198 t1 t2)). Qed.
Lemma lem1309201 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1309200 t1 t2 t3). Qed.
Lemma lem1309202 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1309203 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1309202 t1 t2 t3) (@lem1309201 t1 t2 t3)). Qed.
Lemma lem1309204 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1309203 t1 t2 t3)). Qed.
Lemma lem1309205 (x : nadd) : term24 x.
Proof. exact (@lem9784 (term25 x)). Qed.
Lemma lem1309206 (x : nadd) : (term24 x) = (term26 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1309207 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1309206 x) (@lem1309205 x)). Qed.
Lemma lem1309208 (x : nadd) (h1 : term25 x) : term25 x.
Proof. exact (h1). Qed.
Lemma lem1309209 (x : nadd) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1309210 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1309211 (y : nadd) (h1 : term25 y) : term25 y.
Proof. exact (h1). Qed.
Lemma lem1309213 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1309214 (y : nadd) : (term25 y) = (term29 y).
Proof. exact (@lem1309213 (term25 y)). Qed.
Lemma lem1309215 (y : nadd) : (term29 y) = (term25 y).
Proof. exact (SYM (@lem1309214 y)). Qed.
Lemma lem1309216 (y : nadd) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1309219 (x : nadd) (y : nadd) (h1 : term30 x y) : term30 x y.
Proof. exact (h1). Qed.
Lemma lem1309220 (x : nadd) (y : nadd) : term31 x y.
Proof. exact (fun h0 : term30 x y => @lem1309219 x y h0). Qed.
Lemma lem1309221 (x : nadd) (y : nadd) (h1 : term31 x y) : term31 x y.
Proof. exact (h1). Qed.
Lemma lem1309222 (x : nadd) (y : nadd) (h1 : term30 x y) : term30 x y.
Proof. exact (h1). Qed.
Lemma lem1309223 (x : nadd) (y : nadd) (h1 : term31 x y) (h2 : term30 x y) : term30 x y.
Proof. exact (@lem1309221 x y h1 (@lem1309222 x y h2)). Qed.
Lemma lem1309224 (x : nadd) (y : nadd) (h1 : term30 x y) : term32 x y.
Proof. exact (fun h0 : term31 x y => @lem1309223 x y h0 h1). Qed.
Lemma lem1309225 (x : nadd) (y : nadd) (h1 : term31 x y) : term31 x y.
Proof. exact (h1). Qed.
Lemma lem1309226 (x : nadd) (y : nadd) (h1 : term31 x y) (h2 : term30 x y) : term30 x y.
Proof. exact (@lem1309224 x y h2 (@lem1309225 x y h1)). Qed.
Lemma lem1309227 (x : nadd) (y : nadd) (h1 : term31 x y) : term31 x y.
Proof. exact (fun h0 : term30 x y => @lem1309226 x y h1 h0). Qed.
Lemma lem1309228 (x : nadd) (y : nadd) : term33 x y.
Proof. exact (fun h0 : term31 x y => @lem1309227 x y h0). Qed.
Lemma lem1309231 (x : nadd) (y : nadd) : term31 x y.
Proof. exact (@lem1309228 x y (@lem1309220 x y)). Qed.
Lemma lem1309257 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1309258 : term34 = term35.
Proof. exact (@lem1309257 term7). Qed.
Lemma lem1309275 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1309276 : term37 = term38.
Proof. exact (MK_COMB (@lem1309275) (@lem1309258)). Qed.
Lemma lem1309279 (y : nadd) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem1309280 (y : nadd) : (term40 y) = (term41 y).
Proof. exact (MK_COMB (@lem1309279 y) (@lem1309276)). Qed.
Lemma lem1309283 (x : nadd) : (term42 x) = (term42 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1309284 (x : nadd) (y : nadd) : (term43 x y) = (term44 x y).
Proof. exact (MK_COMB (@lem1309283 x) (@lem1309280 y)). Qed.
Lemma lem1309287 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1309288 (x : nadd) (y : nadd) : (term30 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1309287 x y) (@lem1309284 x y)). Qed.
Lemma lem1309291 (y : nadd) : (term47 y) = (term48 y).
Proof. exact (fun_ext (fun x : nadd => @lem1309288 x y)). Qed.
Lemma lem1309292 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309293 (y : nadd) : (term49 y) = (term50 y).
Proof. exact (MK_COMB (@lem1309292) (@lem1309291 y)). Qed.
Lemma lem1309298 : term51 = term52.
Proof. exact (fun_ext (fun y : nadd => @lem1309293 y)). Qed.
Lemma lem1309299 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309308 : term53 = term54.
Proof. exact (MK_COMB (@lem1309299) (@lem1309298)). Qed.
Lemma lem1309317 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term13 y x z).
Proof. exact (eq_refl (term13 y x z)). Qed.
Lemma lem1309318 (y : nadd) (x : nadd) : (term55 y x) = (term55 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1309317 y x z)). Qed.
Lemma lem1309319 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309320 (y : nadd) (x : nadd) : (term11 y x) = (term11 y x).
Proof. exact (MK_COMB (@lem1309319) (@lem1309318 y x)). Qed.
Lemma lem1309321 (x : nadd) : (term56 x) = (term56 x).
Proof. exact (fun_ext (fun y : nadd => @lem1309320 y x)). Qed.
Lemma lem1309322 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309323 (x : nadd) : (term9 x) = (term9 x).
Proof. exact (MK_COMB (@lem1309322) (@lem1309321 x)). Qed.
Lemma lem1309324 : term57 = term57.
Proof. exact (fun_ext (fun x : nadd => @lem1309323 x)). Qed.
Lemma lem1309325 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309326 : term7 = term7.
Proof. exact (MK_COMB (@lem1309325) (@lem1309324)). Qed.
Lemma lem1309327 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1309328 : term35 = term35.
Proof. exact (MK_COMB (@lem1309327) (@lem1309326)). Qed.
Lemma lem1309333 (y : nadd) (x : nadd) : ((nadd_eq x y) = (nadd_eq y x)) = ((nadd_eq x y) = (nadd_eq y x)).
Proof. exact (eq_refl ((nadd_eq x y) = (nadd_eq y x))). Qed.
Lemma lem1309334 (x : nadd) : (term58 x) = (term58 x).
Proof. exact (fun_ext (fun y : nadd => @lem1309333 y x)). Qed.
Lemma lem1309335 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309336 (x : nadd) : (term59 x) = (term59 x).
Proof. exact (MK_COMB (@lem1309335) (@lem1309334 x)). Qed.
Lemma lem1309337 : term60 = term60.
Proof. exact (fun_ext (fun x : nadd => @lem1309336 x)). Qed.
Lemma lem1309338 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309339 : term61 = term61.
Proof. exact (MK_COMB (@lem1309338) (@lem1309337)). Qed.
Lemma lem1309340 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1309341 : term36 = term36.
Proof. exact (MK_COMB (@lem1309340) (@lem1309339)). Qed.
Lemma lem1309342 : term38 = term38.
Proof. exact (MK_COMB (@lem1309341) (@lem1309328)). Qed.
Lemma lem1309347 (y : nadd) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem1309348 (y : nadd) : (term41 y) = (term41 y).
Proof. exact (MK_COMB (@lem1309347 y) (@lem1309342)). Qed.
Lemma lem1309351 (x : nadd) : (term42 x) = (term42 x).
Proof. exact (eq_refl (term42 x)). Qed.
Lemma lem1309352 (x : nadd) (y : nadd) : (term44 x y) = (term44 x y).
Proof. exact (MK_COMB (@lem1309351 x) (@lem1309348 y)). Qed.
Lemma lem1309355 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1309356 (x : nadd) (y : nadd) : (term46 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1309355 x y) (@lem1309352 x y)). Qed.
Lemma lem1309357 (y : nadd) : (term48 y) = (term48 y).
Proof. exact (fun_ext (fun x : nadd => @lem1309356 x y)). Qed.
Lemma lem1309358 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309359 (y : nadd) : (term50 y) = (term50 y).
Proof. exact (MK_COMB (@lem1309358) (@lem1309357 y)). Qed.
Lemma lem1309360 : term52 = term52.
Proof. exact (fun_ext (fun y : nadd => @lem1309359 y)). Qed.
Lemma lem1309361 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309362 : term54 = term54.
Proof. exact (MK_COMB (@lem1309361) (@lem1309360)). Qed.
Lemma lem1309419 : term53 = term54.
Proof. exact (TRANS (@lem1309308) (@lem1309362)). Qed.
Lemma lem1309420 : term54 = term53.
Proof. exact (SYM (@lem1309419)). Qed.
Lemma lem1309424 (h1 : term61) : term61.
Proof. exact (h1). Qed.
Lemma lem1309425 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1309431 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1309437 (x : nadd) (h1 : term25 x) : term25 x.
Proof. exact (h1). Qed.
Lemma lem1309443 (y : nadd) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1309458 (y : nadd) (x : nadd) : ((nadd_eq x y) = (nadd_eq y x)) = (term62 y x).
Proof. exact (@lem17784 (nadd_eq x y) (nadd_eq y x)). Qed.
Lemma lem1309459 (x : nadd) : (term58 x) = (term63 x).
Proof. exact (fun_ext (fun y : nadd => @lem1309458 y x)). Qed.
Lemma lem1309460 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309461 (x : nadd) : (term59 x) = (term64 x).
Proof. exact (MK_COMB (@lem1309460) (@lem1309459 x)). Qed.
Lemma lem1309462 : term60 = term65.
Proof. exact (fun_ext (fun x : nadd => @lem1309461 x)). Qed.
Lemma lem1309463 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309464 : term61 = term66.
Proof. exact (MK_COMB (@lem1309463) (@lem1309462)). Qed.
Lemma lem1309470 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1309471 (P : nadd -> Prop) (Q : nadd -> Prop) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem1309470 nadd P Q). Qed.
Lemma lem1309472 (x : nadd) : (term71 x) = (term72 x).
Proof. exact (@lem1309471 (term73 x) (term74 x)). Qed.
Lemma lem1309473 (y : nadd) (x : nadd) : (term75 x y) = (term76 y x).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1309474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1309475 (y : nadd) (x : nadd) : (term77 x y) = (term78 y x).
Proof. exact (MK_COMB (@lem1309474) (@lem1309473 y x)). Qed.
Lemma lem1309476 (y : nadd) (x : nadd) : (term79 x y) = (term80 y x).
Proof. exact (eq_refl (term79 x y)). Qed.
Lemma lem1309477 (y : nadd) (x : nadd) : (term81 x y) = (term62 y x).
Proof. exact (MK_COMB (@lem1309475 y x) (@lem1309476 y x)). Qed.
Lemma lem1309478 (x : nadd) : (term82 x) = (term63 x).
Proof. exact (fun_ext (fun y : nadd => @lem1309477 y x)). Qed.
Lemma lem1309479 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309480 (x : nadd) : (term71 x) = (term64 x).
Proof. exact (MK_COMB (@lem1309479) (@lem1309478 x)). Qed.
Lemma lem1309481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1309482 (x : nadd) : (term83 x) = (term84 x).
Proof. exact (MK_COMB (@lem1309481) (@lem1309480 x)). Qed.
Lemma lem1309483 (y : nadd) (x : nadd) : (term75 x y) = (term76 y x).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1309484 (x : nadd) : (term85 x) = (term73 x).
Proof. exact (fun_ext (fun y : nadd => @lem1309483 y x)). Qed.
Lemma lem1309485 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309486 (x : nadd) : (term86 x) = (term87 x).
Proof. exact (MK_COMB (@lem1309485) (@lem1309484 x)). Qed.
Lemma lem1309487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1309488 (x : nadd) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem1309487) (@lem1309486 x)). Qed.
Lemma lem1309489 (y : nadd) (x : nadd) : (term79 x y) = (term80 y x).
Proof. exact (eq_refl (term79 x y)). Qed.
Lemma lem1309490 (x : nadd) : (term90 x) = (term74 x).
Proof. exact (fun_ext (fun y : nadd => @lem1309489 y x)). Qed.
Lemma lem1309491 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309492 (x : nadd) : (term91 x) = (term92 x).
Proof. exact (MK_COMB (@lem1309491) (@lem1309490 x)). Qed.
Lemma lem1309493 (x : nadd) : (term72 x) = (term93 x).
Proof. exact (MK_COMB (@lem1309488 x) (@lem1309492 x)). Qed.
Lemma lem1309494 (x : nadd) : ((term71 x) = (term72 x)) = ((term64 x) = (term93 x)).
Proof. exact (MK_COMB (@lem1309482 x) (@lem1309493 x)). Qed.
Lemma lem1309495 (x : nadd) : (term64 x) = (term93 x).
Proof. exact (EQ_MP (@lem1309494 x) (@lem1309472 x)). Qed.
Lemma lem1309592 : term65 = term94.
Proof. exact (fun_ext (fun x : nadd => @lem1309495 x)). Qed.
Lemma lem1309593 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309594 : term66 = term95.
Proof. exact (MK_COMB (@lem1309593) (@lem1309592)). Qed.
Lemma lem1309596 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1309597 (P : nadd -> Prop) (Q : nadd -> Prop) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem1309596 nadd P Q). Qed.
Lemma lem1309598 : term96 = term97.
Proof. exact (@lem1309597 term98 term99). Qed.
Lemma lem1309599 (x : nadd) : (term100 x) = (term87 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1309600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1309601 (x : nadd) : (term101 x) = (term89 x).
Proof. exact (MK_COMB (@lem1309600) (@lem1309599 x)). Qed.
Lemma lem1309602 (x : nadd) : (term102 x) = (term92 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1309603 (x : nadd) : (term103 x) = (term93 x).
Proof. exact (MK_COMB (@lem1309601 x) (@lem1309602 x)). Qed.
Lemma lem1309604 : term104 = term94.
Proof. exact (fun_ext (fun x : nadd => @lem1309603 x)). Qed.
Lemma lem1309605 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309606 : term96 = term95.
Proof. exact (MK_COMB (@lem1309605) (@lem1309604)). Qed.
Lemma lem1309607 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1309608 : term105 = term106.
Proof. exact (MK_COMB (@lem1309607) (@lem1309606)). Qed.
Lemma lem1309609 (x : nadd) : (term100 x) = (term87 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1309610 : term107 = term98.
Proof. exact (fun_ext (fun x : nadd => @lem1309609 x)). Qed.
Lemma lem1309611 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309612 : term108 = term109.
Proof. exact (MK_COMB (@lem1309611) (@lem1309610)). Qed.
Lemma lem1309613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1309614 : term110 = term111.
Proof. exact (MK_COMB (@lem1309613) (@lem1309612)). Qed.
Lemma lem1309615 (x : nadd) : (term102 x) = (term92 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1309616 : term112 = term99.
Proof. exact (fun_ext (fun x : nadd => @lem1309615 x)). Qed.
Lemma lem1309617 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309618 : term113 = term114.
Proof. exact (MK_COMB (@lem1309617) (@lem1309616)). Qed.
Lemma lem1309619 : term97 = term115.
Proof. exact (MK_COMB (@lem1309614) (@lem1309618)). Qed.
Lemma lem1309620 : (term96 = term97) = (term95 = term115).
Proof. exact (MK_COMB (@lem1309608) (@lem1309619)). Qed.
Lemma lem1309621 : term95 = term115.
Proof. exact (EQ_MP (@lem1309620) (@lem1309598)). Qed.
Lemma lem1309728 : term66 = term115.
Proof. exact (TRANS (@lem1309594) (@lem1309621)). Qed.
Lemma lem1309729 : term61 = term115.
Proof. exact (TRANS (@lem1309464) (@lem1309728)). Qed.
Lemma lem1309730 (h1 : term61) : term115.
Proof. exact (EQ_MP (@lem1309729) (@lem1309424 h1)). Qed.
Lemma lem1309737 (x : nadd) (y : nadd) (z : nadd) : (term116 x y z) = (term117 x y z).
Proof. exact (@lem17045 (nadd_eq x y) (nadd_eq y z)). Qed.
Lemma lem1309738 (x : nadd) (z : nadd) : (nadd_eq x z) = (nadd_eq x z).
Proof. exact (eq_refl (nadd_eq x z)). Qed.
Lemma lem1309739 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1309740 (x : nadd) (y : nadd) (z : nadd) : (term118 x y z) = (term119 x y z).
Proof. exact (MK_COMB (@lem1309739) (@lem1309737 x y z)). Qed.
Lemma lem1309741 (y : nadd) (x : nadd) (z : nadd) : (term120 y x z) = (term121 y x z).
Proof. exact (MK_COMB (@lem1309740 x y z) (@lem1309738 x z)). Qed.
Lemma lem1309742 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term120 y x z).
Proof. exact (@lem17265 (term14 x y z) (nadd_eq x z)). Qed.
Lemma lem1309743 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term121 y x z).
Proof. exact (TRANS (@lem1309742 y x z) (@lem1309741 y x z)). Qed.
Lemma lem1309744 (y : nadd) (x : nadd) : (term55 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1309743 y x z)). Qed.
Lemma lem1309745 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309746 (y : nadd) (x : nadd) : (term11 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1309745) (@lem1309744 y x)). Qed.
Lemma lem1309747 (x : nadd) : (term56 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1309746 y x)). Qed.
Lemma lem1309748 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309749 (x : nadd) : (term9 x) = (term125 x).
Proof. exact (MK_COMB (@lem1309748) (@lem1309747 x)). Qed.
Lemma lem1309750 : term57 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1309749 x)). Qed.
Lemma lem1309751 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309812 : term7 = term127.
Proof. exact (MK_COMB (@lem1309751) (@lem1309750)). Qed.
Lemma lem1309813 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1309812) (@lem1309425 h1)). Qed.
Lemma lem1309819 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1309829 (x : nadd) (h1 : term25 x) : term25 x.
Proof. exact (h1). Qed.
Lemma lem1309841 (y : nadd) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1309856 (y : nadd) (x : nadd) : (term80 y x) = (term80 y x).
Proof. exact (eq_refl (term80 y x)). Qed.
Lemma lem1309857 (x : nadd) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : nadd => @lem1309856 y x)). Qed.
Lemma lem1309858 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309859 (x : nadd) : (term92 x) = (term92 x).
Proof. exact (MK_COMB (@lem1309858) (@lem1309857 x)). Qed.
Lemma lem1309860 : term99 = term99.
Proof. exact (fun_ext (fun x : nadd => @lem1309859 x)). Qed.
Lemma lem1309861 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309862 : term114 = term114.
Proof. exact (MK_COMB (@lem1309861) (@lem1309860)). Qed.
Lemma lem1309877 (y : nadd) (x : nadd) : (term76 y x) = (term76 y x).
Proof. exact (eq_refl (term76 y x)). Qed.
Lemma lem1309878 (x : nadd) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun y : nadd => @lem1309877 y x)). Qed.
Lemma lem1309879 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309880 (x : nadd) : (term87 x) = (term87 x).
Proof. exact (MK_COMB (@lem1309879) (@lem1309878 x)). Qed.
Lemma lem1309881 : term98 = term98.
Proof. exact (fun_ext (fun x : nadd => @lem1309880 x)). Qed.
Lemma lem1309882 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309883 : term109 = term109.
Proof. exact (MK_COMB (@lem1309882) (@lem1309881)). Qed.
Lemma lem1309884 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1309885 : term111 = term111.
Proof. exact (MK_COMB (@lem1309884) (@lem1309883)). Qed.
Lemma lem1309886 : term115 = term115.
Proof. exact (MK_COMB (@lem1309885) (@lem1309862)). Qed.
Lemma lem1309887 (h1 : term61) : term115.
Proof. exact (EQ_MP (@lem1309886) (@lem1309730 h1)). Qed.
Lemma lem1309912 (y : nadd) (x : nadd) (z : nadd) : (term121 y x z) = (term121 y x z).
Proof. exact (eq_refl (term121 y x z)). Qed.
Lemma lem1309913 (y : nadd) (x : nadd) : (term122 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1309912 y x z)). Qed.
Lemma lem1309914 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309915 (y : nadd) (x : nadd) : (term123 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1309914) (@lem1309913 y x)). Qed.
Lemma lem1309916 (x : nadd) : (term124 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1309915 y x)). Qed.
Lemma lem1309917 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309918 (x : nadd) : (term125 x) = (term125 x).
Proof. exact (MK_COMB (@lem1309917) (@lem1309916 x)). Qed.
Lemma lem1309919 : term126 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1309918 x)). Qed.
Lemma lem1309920 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309921 : term127 = term127.
Proof. exact (MK_COMB (@lem1309920) (@lem1309919)). Qed.
Lemma lem1309922 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1309921) (@lem1309813 h1)). Qed.
Lemma lem1309923 (h1 : term61) : term114.
Proof. exact (proj2 (@lem1309887 h1)). Qed.
Lemma lem1309928 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1309932 (x : nadd) (h1 : term25 x) : term25 x.
Proof. exact (h1). Qed.
Lemma lem1309936 (y : nadd) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1309950 (y : nadd) (x : nadd) (z : nadd) : (term121 y x z) = (term121 y x z).
Proof. exact (eq_refl (term121 y x z)). Qed.
Lemma lem1309951 (y : nadd) (x : nadd) : (term122 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1309950 y x z)). Qed.
Lemma lem1309952 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309953 (y : nadd) (x : nadd) : (term123 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1309952) (@lem1309951 y x)). Qed.
Lemma lem1309954 (x : nadd) : (term124 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1309953 y x)). Qed.
Lemma lem1309955 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309956 (x : nadd) : (term125 x) = (term125 x).
Proof. exact (MK_COMB (@lem1309955) (@lem1309954 x)). Qed.
Lemma lem1309957 : term126 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1309956 x)). Qed.
Lemma lem1309958 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309960 : term127 = term127.
Proof. exact (MK_COMB (@lem1309958) (@lem1309957)). Qed.
Lemma lem1309961 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1309960) (@lem1309922 h1)). Qed.
Lemma lem1309985 (y : nadd) (x : nadd) : (term80 y x) = (term80 y x).
Proof. exact (eq_refl (term80 y x)). Qed.
Lemma lem1309986 (x : nadd) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : nadd => @lem1309985 y x)). Qed.
Lemma lem1309987 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309988 (x : nadd) : (term92 x) = (term92 x).
Proof. exact (MK_COMB (@lem1309987) (@lem1309986 x)). Qed.
Lemma lem1309989 : term99 = term99.
Proof. exact (fun_ext (fun x : nadd => @lem1309988 x)). Qed.
Lemma lem1309990 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1309992 : term114 = term114.
Proof. exact (MK_COMB (@lem1309990) (@lem1309989)). Qed.
Lemma lem1309993 (h1 : term61) : term114.
Proof. exact (EQ_MP (@lem1309992) (@lem1309923 h1)). Qed.
Lemma lem1309994 (_23354 : nadd) (h1 : term7) : term128 _23354.
Proof. exact (@lem1309961 h1 _23354). Qed.
Lemma lem1309995 (_23354 : nadd) : (term128 _23354) = (term125 _23354).
Proof. exact (eq_refl (term128 _23354)). Qed.
Lemma lem1309996 (_23354 : nadd) (h1 : term7) : term125 _23354.
Proof. exact (EQ_MP (@lem1309995 _23354) (@lem1309994 _23354 h1)). Qed.
Lemma lem1309997 (_23354 : nadd) (_23355 : nadd) (h1 : term7) : term129 _23354 _23355.
Proof. exact (@lem1309996 _23354 h1 _23355). Qed.
Lemma lem1309998 (_23355 : nadd) (_23354 : nadd) : (term129 _23354 _23355) = (term123 _23355 _23354).
Proof. exact (eq_refl (term129 _23354 _23355)). Qed.
Lemma lem1309999 (_23355 : nadd) (_23354 : nadd) (h1 : term7) : term123 _23355 _23354.
Proof. exact (EQ_MP (@lem1309998 _23355 _23354) (@lem1309997 _23354 _23355 h1)). Qed.
Lemma lem1310000 (_23355 : nadd) (_23354 : nadd) (_23356 : nadd) (h1 : term7) : term130 _23355 _23354 _23356.
Proof. exact (@lem1309999 _23355 _23354 h1 _23356). Qed.
Lemma lem1310001 (_23355 : nadd) (_23354 : nadd) (_23356 : nadd) : (term130 _23355 _23354 _23356) = (term121 _23355 _23354 _23356).
Proof. exact (eq_refl (term130 _23355 _23354 _23356)). Qed.
Lemma lem1310002 (_23355 : nadd) (_23354 : nadd) (_23356 : nadd) (h1 : term7) : term121 _23355 _23354 _23356.
Proof. exact (EQ_MP (@lem1310001 _23355 _23354 _23356) (@lem1310000 _23355 _23354 _23356 h1)). Qed.
Lemma lem1310009 (_23359 : nadd) (h1 : term61) : term102 _23359.
Proof. exact (@lem1309993 h1 _23359). Qed.
Lemma lem1310010 (_23359 : nadd) : (term102 _23359) = (term92 _23359).
Proof. exact (eq_refl (term102 _23359)). Qed.
Lemma lem1310011 (_23359 : nadd) (h1 : term61) : term92 _23359.
Proof. exact (EQ_MP (@lem1310010 _23359) (@lem1310009 _23359 h1)). Qed.
Lemma lem1310012 (_23359 : nadd) (_23360 : nadd) (h1 : term61) : term79 _23359 _23360.
Proof. exact (@lem1310011 _23359 h1 _23360). Qed.
Lemma lem1310013 (_23360 : nadd) (_23359 : nadd) : (term79 _23359 _23360) = (term80 _23360 _23359).
Proof. exact (eq_refl (term79 _23359 _23360)). Qed.
Lemma lem1310016 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1310018 (x : nadd) (h1 : term25 x) : term25 x.
Proof. exact (h1). Qed.
Lemma lem1310020 (y : nadd) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1310031 (_23355 : nadd) (_23354 : nadd) (_23356 : nadd) : (term121 _23355 _23354 _23356) = (term131 _23355 _23354 _23356).
Proof. exact (@lem1309204 (term132 _23354 _23355) (term132 _23355 _23356) (nadd_eq _23354 _23356)). Qed.
Lemma lem1310032 (_23355 : nadd) (_23354 : nadd) (_23356 : nadd) (h1 : term7) : term131 _23355 _23354 _23356.
Proof. exact (EQ_MP (@lem1310031 _23355 _23354 _23356) (@lem1310002 _23355 _23354 _23356 h1)). Qed.
Lemma lem1310044 (_23360 : nadd) (_23359 : nadd) (h1 : term61) : term80 _23360 _23359.
Proof. exact (EQ_MP (@lem1310013 _23360 _23359) (@lem1310012 _23359 _23360 h1)). Qed.
Lemma lem1310046 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1310047 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term133 x y.
Proof. exact (fun h0 : term132 x y => @lem1310046 x y h1). Qed.
Lemma lem1310049 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1310050 (x : nadd) (y : nadd) : (term133 x y) = (nadd_eq x y).
Proof. exact (@lem1310049 (nadd_eq x y)). Qed.
Lemma lem1310051 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (EQ_MP (@lem1310050 x y) (@lem1310047 x y h1)). Qed.
Lemma lem1310057 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1310058 (_23359 : nadd) (_23360 : nadd) : (term80 _23360 _23359) = (term76 _23359 _23360).
Proof. exact (@lem1310057 (nadd_eq _23360 _23359) (term132 _23359 _23360)). Qed.
Lemma lem1310064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1310065 (_23359 : nadd) (_23360 : nadd) : (term135 _23360 _23359) = (term136 _23359 _23360).
Proof. exact (MK_COMB (@lem1310064) (@lem1310058 _23359 _23360)). Qed.
Lemma lem1310071 (_23359 : nadd) (_23360 : nadd) : (term76 _23359 _23360) = (term76 _23359 _23360).
Proof. exact (eq_refl (term76 _23359 _23360)). Qed.
Lemma lem1310072 (_23359 : nadd) (_23360 : nadd) : ((term80 _23360 _23359) = (term76 _23359 _23360)) = ((term76 _23359 _23360) = (term76 _23359 _23360)).
Proof. exact (MK_COMB (@lem1310065 _23359 _23360) (@lem1310071 _23359 _23360)). Qed.
Lemma lem1310074 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1310075 (x : Prop) : (x = x) = True.
Proof. exact (@lem1310074 Prop x). Qed.
Lemma lem1310076 (_23359 : nadd) (_23360 : nadd) : ((term76 _23359 _23360) = (term76 _23359 _23360)) = True.
Proof. exact (@lem1310075 (term76 _23359 _23360)). Qed.
Lemma lem1310077 (_23359 : nadd) (_23360 : nadd) : ((term80 _23360 _23359) = (term76 _23359 _23360)) = True.
Proof. exact (TRANS (@lem1310072 _23359 _23360) (@lem1310076 _23359 _23360)). Qed.
Lemma lem1310078 (_23359 : nadd) (_23360 : nadd) : True = ((term80 _23360 _23359) = (term76 _23359 _23360)).
Proof. exact (SYM (@lem1310077 _23359 _23360)). Qed.
Lemma lem1310079 (_23359 : nadd) (_23360 : nadd) : (term80 _23360 _23359) = (term76 _23359 _23360).
Proof. exact (EQ_MP (@lem1310078 _23359 _23360) (@lem0)). Qed.
Lemma lem1310080 (_23359 : nadd) (_23360 : nadd) (h1 : term61) : term76 _23359 _23360.
Proof. exact (EQ_MP (@lem1310079 _23359 _23360) (@lem1310044 _23360 _23359 h1)). Qed.
Lemma lem1310082 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1310083 (_23360 : nadd) (_23359 : nadd) : (term76 _23359 _23360) = (term138 _23360 _23359).
Proof. exact (@lem1310082 (term132 _23359 _23360) (nadd_eq _23360 _23359)). Qed.
Lemma lem1310085 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1310086 (_23359 : nadd) (_23360 : nadd) : (term140 _23359 _23360) = (nadd_eq _23359 _23360).
Proof. exact (@lem1310085 (nadd_eq _23359 _23360)). Qed.
Lemma lem1310087 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1310088 (_23359 : nadd) (_23360 : nadd) : (term141 _23359 _23360) = (term45 _23359 _23360).
Proof. exact (MK_COMB (@lem1310087) (@lem1310086 _23359 _23360)). Qed.
Lemma lem1310089 (_23360 : nadd) (_23359 : nadd) : (nadd_eq _23360 _23359) = (nadd_eq _23360 _23359).
Proof. exact (eq_refl (nadd_eq _23360 _23359)). Qed.
Lemma lem1310090 (_23360 : nadd) (_23359 : nadd) : (term138 _23360 _23359) = (term142 _23360 _23359).
Proof. exact (MK_COMB (@lem1310088 _23359 _23360) (@lem1310089 _23360 _23359)). Qed.
Lemma lem1310091 (_23360 : nadd) (_23359 : nadd) : (term76 _23359 _23360) = (term142 _23360 _23359).
Proof. exact (TRANS (@lem1310083 _23360 _23359) (@lem1310090 _23360 _23359)). Qed.
Lemma lem1310094 (_23360 : nadd) (_23359 : nadd) (h1 : term61) : term142 _23360 _23359.
Proof. exact (EQ_MP (@lem1310091 _23360 _23359) (@lem1310080 _23359 _23360 h1)). Qed.
Lemma lem1310095 (y : nadd) (x : nadd) (h1 : term61) : term142 y x.
Proof. exact (@lem1310094 y x h1). Qed.
Lemma lem1310098 (x : nadd) (y : nadd) (h1 : term61) (h2 : nadd_eq x y) : nadd_eq y x.
Proof. exact (@lem1310095 y x h1 (@lem1310051 x y h2)). Qed.
Lemma lem1310099 (x : nadd) (y : nadd) (h1 : term61) (h2 : nadd_eq x y) : term133 y x.
Proof. exact (fun h0 : term132 y x => @lem1310098 x y h1 h2). Qed.
Lemma lem1310101 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1310102 (y : nadd) (x : nadd) : (term133 y x) = (nadd_eq y x).
Proof. exact (@lem1310101 (nadd_eq y x)). Qed.
Lemma lem1310103 (x : nadd) (y : nadd) (h1 : term61) (h2 : nadd_eq x y) : nadd_eq y x.
Proof. exact (EQ_MP (@lem1310102 y x) (@lem1310099 x y h1 h2)). Qed.
Lemma lem1310105 (x : nadd) (h1 : term25 x) : term25 x.
Proof. exact (h1). Qed.
Lemma lem1310106 (x : nadd) (h1 : term25 x) : term143 x.
Proof. exact (fun h0 : term27 x => @lem1310105 x h1). Qed.
Lemma lem1310108 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1310109 (x : nadd) : (term143 x) = (term25 x).
Proof. exact (@lem1310108 (term25 x)). Qed.
Lemma lem1310110 (x : nadd) (h1 : term25 x) : term25 x.
Proof. exact (EQ_MP (@lem1310109 x) (@lem1310106 x h1)). Qed.
Lemma lem1310126 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1310127 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : (term144 _23355 _23354 _23356) = (term145 _23354 _23355 _23356).
Proof. exact (@lem1310126 (nadd_eq _23354 _23356) (term132 _23355 _23356)). Qed.
Lemma lem1310133 (_23354 : nadd) (_23355 : nadd) : (term146 _23354 _23355) = (term146 _23354 _23355).
Proof. exact (eq_refl (term146 _23354 _23355)). Qed.
Lemma lem1310134 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : (term131 _23355 _23354 _23356) = (term147 _23354 _23355 _23356).
Proof. exact (MK_COMB (@lem1310133 _23354 _23355) (@lem1310127 _23354 _23355 _23356)). Qed.
Lemma lem1310138 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1310139 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : (term147 _23354 _23355 _23356) = (term148 _23354 _23355 _23356).
Proof. exact (@lem1310138 (nadd_eq _23354 _23356) (term132 _23354 _23355) (term132 _23355 _23356)). Qed.
Lemma lem1310155 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : (term131 _23355 _23354 _23356) = (term148 _23354 _23355 _23356).
Proof. exact (TRANS (@lem1310134 _23354 _23355 _23356) (@lem1310139 _23354 _23355 _23356)). Qed.
Lemma lem1310156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1310157 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : (term149 _23355 _23354 _23356) = (term150 _23354 _23355 _23356).
Proof. exact (MK_COMB (@lem1310156) (@lem1310155 _23354 _23355 _23356)). Qed.
Lemma lem1310173 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : (term148 _23354 _23355 _23356) = (term148 _23354 _23355 _23356).
Proof. exact (eq_refl (term148 _23354 _23355 _23356)). Qed.
Lemma lem1310174 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : ((term131 _23355 _23354 _23356) = (term148 _23354 _23355 _23356)) = ((term148 _23354 _23355 _23356) = (term148 _23354 _23355 _23356)).
Proof. exact (MK_COMB (@lem1310157 _23354 _23355 _23356) (@lem1310173 _23354 _23355 _23356)). Qed.
Lemma lem1310176 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1310177 (x : Prop) : (x = x) = True.
Proof. exact (@lem1310176 Prop x). Qed.
Lemma lem1310178 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : ((term148 _23354 _23355 _23356) = (term148 _23354 _23355 _23356)) = True.
Proof. exact (@lem1310177 (term148 _23354 _23355 _23356)). Qed.
Lemma lem1310179 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : ((term131 _23355 _23354 _23356) = (term148 _23354 _23355 _23356)) = True.
Proof. exact (TRANS (@lem1310174 _23354 _23355 _23356) (@lem1310178 _23354 _23355 _23356)). Qed.
Lemma lem1310180 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : True = ((term131 _23355 _23354 _23356) = (term148 _23354 _23355 _23356)).
Proof. exact (SYM (@lem1310179 _23354 _23355 _23356)). Qed.
Lemma lem1310181 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : (term131 _23355 _23354 _23356) = (term148 _23354 _23355 _23356).
Proof. exact (EQ_MP (@lem1310180 _23354 _23355 _23356) (@lem0)). Qed.
Lemma lem1310182 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) (h1 : term7) : term148 _23354 _23355 _23356.
Proof. exact (EQ_MP (@lem1310181 _23354 _23355 _23356) (@lem1310032 _23355 _23354 _23356 h1)). Qed.
Lemma lem1310184 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1310185 (_23355 : nadd) (_23354 : nadd) (_23356 : nadd) : (term148 _23354 _23355 _23356) = (term151 _23355 _23354 _23356).
Proof. exact (@lem1310184 (term117 _23354 _23355 _23356) (nadd_eq _23354 _23356)). Qed.
Lemma lem1310187 (a : Prop) (b : Prop) : (term152 a b) = (term153 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1310188 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : (term154 _23354 _23355 _23356) = (term155 _23354 _23355 _23356).
Proof. exact (@lem1310187 (term132 _23354 _23355) (term132 _23355 _23356)). Qed.
Lemma lem1310190 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1310191 (_23354 : nadd) (_23355 : nadd) : (term140 _23354 _23355) = (nadd_eq _23354 _23355).
Proof. exact (@lem1310190 (nadd_eq _23354 _23355)). Qed.
Lemma lem1310192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1310193 (_23354 : nadd) (_23355 : nadd) : (term156 _23354 _23355) = (term157 _23354 _23355).
Proof. exact (MK_COMB (@lem1310192) (@lem1310191 _23354 _23355)). Qed.
Lemma lem1310195 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1310196 (_23355 : nadd) (_23356 : nadd) : (term140 _23355 _23356) = (nadd_eq _23355 _23356).
Proof. exact (@lem1310195 (nadd_eq _23355 _23356)). Qed.
Lemma lem1310197 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : (term155 _23354 _23355 _23356) = (term14 _23354 _23355 _23356).
Proof. exact (MK_COMB (@lem1310193 _23354 _23355) (@lem1310196 _23355 _23356)). Qed.
Lemma lem1310198 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : (term154 _23354 _23355 _23356) = (term14 _23354 _23355 _23356).
Proof. exact (TRANS (@lem1310188 _23354 _23355 _23356) (@lem1310197 _23354 _23355 _23356)). Qed.
Lemma lem1310199 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1310200 (_23354 : nadd) (_23355 : nadd) (_23356 : nadd) : (term158 _23354 _23355 _23356) = (term159 _23354 _23355 _23356).
Proof. exact (MK_COMB (@lem1310199) (@lem1310198 _23354 _23355 _23356)). Qed.
Lemma lem1310201 (_23354 : nadd) (_23356 : nadd) : (nadd_eq _23354 _23356) = (nadd_eq _23354 _23356).
Proof. exact (eq_refl (nadd_eq _23354 _23356)). Qed.
Lemma lem1310202 (_23355 : nadd) (_23354 : nadd) (_23356 : nadd) : (term151 _23355 _23354 _23356) = (term13 _23355 _23354 _23356).
Proof. exact (MK_COMB (@lem1310200 _23354 _23355 _23356) (@lem1310201 _23354 _23356)). Qed.
Lemma lem1310203 (_23355 : nadd) (_23354 : nadd) (_23356 : nadd) : (term148 _23354 _23355 _23356) = (term13 _23355 _23354 _23356).
Proof. exact (TRANS (@lem1310185 _23355 _23354 _23356) (@lem1310202 _23355 _23354 _23356)). Qed.
Lemma lem1310205 (y : nadd) (x : nadd) (h1 : term61) (h2 : nadd_eq x y) (h3 : term25 x) : term160 y x.
Proof. exact (conj (@lem1310103 x y h1 h2) (@lem1310110 x h3)). Qed.
Lemma lem1310207 (_23355 : nadd) (_23354 : nadd) (_23356 : nadd) (h1 : term7) : term13 _23355 _23354 _23356.
Proof. exact (EQ_MP (@lem1310203 _23355 _23354 _23356) (@lem1310182 _23354 _23355 _23356 h1)). Qed.
Lemma lem1310208 (x : nadd) (y : nadd) (h1 : term7) : term161 x y.
Proof. exact (@lem1310207 x y term162 h1). Qed.
Lemma lem1310211 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : nadd_eq x y) (h4 : term25 x) : term25 y.
Proof. exact (@lem1310208 x y h1 (@lem1310205 y x h2 h3 h4)). Qed.
Lemma lem1310212 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : nadd_eq x y) (h4 : term25 x) : term143 y.
Proof. exact (fun h0 : term27 y => @lem1310211 y x h1 h2 h3 h4). Qed.
Lemma lem1310214 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1310215 (y : nadd) : (term143 y) = (term25 y).
Proof. exact (@lem1310214 (term25 y)). Qed.
Lemma lem1310216 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : nadd_eq x y) (h4 : term25 x) : term25 y.
Proof. exact (EQ_MP (@lem1310215 y) (@lem1310212 y x h1 h2 h3 h4)). Qed.
Lemma lem1310219 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1310221 (y : nadd) : (term27 y) = (term163 y).
Proof. exact (@lem1310219 (term25 y)). Qed.
Lemma lem1310224 (y : nadd) (h1 : term27 y) : term163 y.
Proof. exact (EQ_MP (@lem1310221 y) (@lem1310020 y h1)). Qed.
Lemma lem1310227 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (@lem1310224 y h3 (@lem1310216 y x h1 h2 h4 h5)). Qed.
Lemma lem1310228 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : term164.
Proof. exact (fun h0 : ~ False => @lem1310227 y x h1 h2 h3 h4 h5). Qed.
Lemma lem1310230 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1310231 : term164 = False.
Proof. exact (@lem1310230 False). Qed.
Lemma lem1310232 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310231) (@lem1310228 y x h1 h2 h3 h4 h5)). Qed.
Lemma lem1310233 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (term27 y) = False.
Proof. exact (prop_ext (fun h6 : term27 y => @lem1310232 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1310020 y h3)). Qed.
Lemma lem1310234 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310233 y x h1 h2 h3 h4 h5) (@lem1310020 y h3)). Qed.
Lemma lem1310235 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (term25 x) = False.
Proof. exact (prop_ext (fun h6 : term25 x => @lem1310234 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1310018 x h5)). Qed.
Lemma lem1310236 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310235 y x h1 h2 h3 h4 h5) (@lem1310018 x h5)). Qed.
Lemma lem1310237 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h6 : nadd_eq x y => @lem1310236 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1310016 x y h4)). Qed.
Lemma lem1310238 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310237 y x h1 h2 h3 h4 h5) (@lem1310016 x y h4)). Qed.
Lemma lem1310239 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (term27 y) = False.
Proof. exact (prop_ext (fun h6 : term27 y => @lem1310238 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1309936 y h3)). Qed.
Lemma lem1310240 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310239 y x h1 h2 h3 h4 h5) (@lem1309936 y h3)). Qed.
Lemma lem1310241 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (term25 x) = False.
Proof. exact (prop_ext (fun h6 : term25 x => @lem1310240 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1309932 x h5)). Qed.
Lemma lem1310242 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310241 y x h1 h2 h3 h4 h5) (@lem1309932 x h5)). Qed.
Lemma lem1310243 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h6 : nadd_eq x y => @lem1310242 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1309928 x y h4)). Qed.
Lemma lem1310244 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310243 y x h1 h2 h3 h4 h5) (@lem1309928 x y h4)). Qed.
Lemma lem1310245 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (term27 y) = False.
Proof. exact (prop_ext (fun h6 : term27 y => @lem1310244 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1309936 y h3)). Qed.
Lemma lem1310246 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310245 y x h1 h2 h3 h4 h5) (@lem1309936 y h3)). Qed.
Lemma lem1310247 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (term25 x) = False.
Proof. exact (prop_ext (fun h6 : term25 x => @lem1310246 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1309932 x h5)). Qed.
Lemma lem1310248 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310247 y x h1 h2 h3 h4 h5) (@lem1309932 x h5)). Qed.
Lemma lem1310249 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h6 : nadd_eq x y => @lem1310248 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1309928 x y h4)). Qed.
Lemma lem1310250 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310249 y x h1 h2 h3 h4 h5) (@lem1309928 x y h4)). Qed.
Lemma lem1310251 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (term27 y) = False.
Proof. exact (prop_ext (fun h6 : term27 y => @lem1310250 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1309841 y h3)). Qed.
Lemma lem1310252 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310251 y x h1 h2 h3 h4 h5) (@lem1309841 y h3)). Qed.
Lemma lem1310253 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (term25 x) = False.
Proof. exact (prop_ext (fun h6 : term25 x => @lem1310252 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1309829 x h5)). Qed.
Lemma lem1310254 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310253 y x h1 h2 h3 h4 h5) (@lem1309829 x h5)). Qed.
Lemma lem1310255 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h6 : nadd_eq x y => @lem1310254 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1309819 x y h4)). Qed.
Lemma lem1310256 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310255 y x h1 h2 h3 h4 h5) (@lem1309819 x y h4)). Qed.
Lemma lem1310257 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (term27 y) = False.
Proof. exact (prop_ext (fun h6 : term27 y => @lem1310256 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1309443 y h3)). Qed.
Lemma lem1310258 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310257 y x h1 h2 h3 h4 h5) (@lem1309443 y h3)). Qed.
Lemma lem1310259 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (term25 x) = False.
Proof. exact (prop_ext (fun h6 : term25 x => @lem1310258 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1309437 x h5)). Qed.
Lemma lem1310260 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310259 y x h1 h2 h3 h4 h5) (@lem1309437 x h5)). Qed.
Lemma lem1310261 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h6 : nadd_eq x y => @lem1310260 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1309431 x y h4)). Qed.
Lemma lem1310262 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : nadd_eq x y) (h5 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310261 y x h1 h2 h3 h4 h5) (@lem1309431 x y h4)). Qed.
Lemma lem1310263 (y : nadd) (x : nadd) (h1 : term61) (h2 : term27 y) (h3 : nadd_eq x y) (h4 : term25 x) : term34.
Proof. exact (fun h0 : term7 => @lem1310262 y x h0 h1 h2 h3 h4). Qed.
Lemma lem1310264 : term34 = term35.
Proof. exact (@lem69 term7). Qed.
Lemma lem1310265 (y : nadd) (x : nadd) (h1 : term61) (h2 : term27 y) (h3 : nadd_eq x y) (h4 : term25 x) : term35.
Proof. exact (EQ_MP (@lem1310264) (@lem1310263 y x h1 h2 h3 h4)). Qed.
Lemma lem1310266 (y : nadd) (x : nadd) (h1 : term27 y) (h2 : nadd_eq x y) (h3 : term25 x) : term38.
Proof. exact (fun h0 : term61 => @lem1310265 y x h0 h1 h2 h3). Qed.
Lemma lem1310267 (y : nadd) (x : nadd) (h1 : nadd_eq x y) (h2 : term25 x) : term41 y.
Proof. exact (fun h0 : term27 y => @lem1310266 y x h0 h1 h2). Qed.
Lemma lem1310268 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term44 x y.
Proof. exact (fun h0 : term25 x => @lem1310267 y x h1 h0). Qed.
Lemma lem1310269 (x : nadd) (y : nadd) : term46 x y.
Proof. exact (fun h0 : nadd_eq x y => @lem1310268 x y h0). Qed.
Lemma lem1310274 (y : nadd) : term50 y.
Proof. exact (fun x : nadd => @lem1310269 x y). Qed.
Lemma lem1310279 : term54.
Proof. exact (fun y : nadd => @lem1310274 y). Qed.
Lemma lem1310280 : term53.
Proof. exact (EQ_MP (@lem1309420) (@lem1310279)). Qed.
Lemma lem1310281 (y : nadd) : term165 y.
Proof. exact (@lem1310280 y). Qed.
Lemma lem1310282 (y : nadd) : (term165 y) = (term49 y).
Proof. exact (eq_refl (term165 y)). Qed.
Lemma lem1310283 (y : nadd) : term49 y.
Proof. exact (EQ_MP (@lem1310282 y) (@lem1310281 y)). Qed.
Lemma lem1310284 (y : nadd) (x : nadd) : term166 y x.
Proof. exact (@lem1310283 y x). Qed.
Lemma lem1310285 (x : nadd) (y : nadd) : (term166 y x) = (term30 x y).
Proof. exact (eq_refl (term166 y x)). Qed.
Lemma lem1310286 (x : nadd) (y : nadd) : term30 x y.
Proof. exact (EQ_MP (@lem1310285 x y) (@lem1310284 y x)). Qed.
Lemma lem1310288 (x : nadd) (y : nadd) : term30 x y.
Proof. exact (@lem1309231 x y (@lem1310286 x y)). Qed.
Lemma lem1310289 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term43 x y.
Proof. exact (@lem1310288 x y (@lem1309210 x y h1)). Qed.
Lemma lem1310290 (y : nadd) (x : nadd) (h1 : nadd_eq x y) (h2 : term25 x) : term40 y.
Proof. exact (@lem1310289 x y h1 (@lem1309208 x h2)). Qed.
Lemma lem1310291 (y : nadd) (x : nadd) (h1 : term27 y) (h2 : nadd_eq x y) (h3 : term25 x) : term37.
Proof. exact (@lem1310290 y x h2 h3 (@lem1309216 y h1)). Qed.
Lemma lem1310292 (y : nadd) (x : nadd) (h1 : term27 y) (h2 : nadd_eq x y) (h3 : term25 x) : term34.
Proof. exact (@lem1310291 y x h1 h2 h3 (@lem1268060)). Qed.
Lemma lem1310293 (y : nadd) (x : nadd) (h1 : term27 y) (h2 : nadd_eq x y) (h3 : term25 x) : False.
Proof. exact (@lem1310292 y x h1 h2 h3 (@lem1268295)). Qed.
Lemma lem1310294 (y : nadd) (x : nadd) (h1 : term27 y) (h2 : nadd_eq x y) (h3 : term25 x) : (term27 y) = False.
Proof. exact (prop_ext (fun h4 : term27 y => @lem1310293 y x h1 h2 h3) (fun h4 : False => @lem1309216 y h1)). Qed.
Lemma lem1310295 (y : nadd) (x : nadd) (h1 : term27 y) (h2 : nadd_eq x y) (h3 : term25 x) : False.
Proof. exact (EQ_MP (@lem1310294 y x h1 h2 h3) (@lem1309216 y h1)). Qed.
Lemma lem1310296 (y : nadd) (x : nadd) (h1 : nadd_eq x y) (h2 : term25 x) : term29 y.
Proof. exact (fun h0 : term27 y => @lem1310295 y x h0 h1 h2). Qed.
Lemma lem1310297 (y : nadd) (x : nadd) (h1 : nadd_eq x y) (h2 : term25 x) : term25 y.
Proof. exact (EQ_MP (@lem1309215 y) (@lem1310296 y x h1 h2)). Qed.
Lemma lem1310298 (x : nadd) : term167 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1310299 (x : nadd) : (term167 x) = (nadd_eq x x).
Proof. exact (eq_refl (term167 x)). Qed.
Lemma lem1310300 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1310299 x) (@lem1310298 x)). Qed.
Lemma lem1310301 (x : nadd) : (nadd_eq x x) = ((nadd_eq x x) = True).
Proof. exact (@lem7 (nadd_eq x x)). Qed.
Lemma lem1310303 (x : nadd) : term168 x.
Proof. exact (@lem1308008 x). Qed.
Lemma lem1310304 (x : nadd) : (term168 x) = ((nadd_inv x) = (term169 x)).
Proof. exact (eq_refl (term168 x)). Qed.
Lemma lem1310308 (x : nadd) : (term25 x) = ((term25 x) = True).
Proof. exact (@lem7 (term25 x)). Qed.
Lemma lem1310310 (y : nadd) : (term25 y) = ((term25 y) = True).
Proof. exact (@lem7 (term25 y)). Qed.
Lemma lem1310315 (x : nadd) : (nadd_inv x) = (term169 x).
Proof. exact (EQ_MP (@lem1310304 x) (@lem1310303 x)). Qed.
Lemma lem1310317 (x : nadd) (h1 : term25 x) : (term25 x) = True.
Proof. exact (EQ_MP (@lem1310308 x) (@lem1309208 x h1)). Qed.
Lemma lem1310318 : (@COND nadd) = (@COND nadd).
Proof. exact (eq_refl (@COND nadd)). Qed.
Lemma lem1310319 (x : nadd) (h1 : term25 x) : (term170 x) = (@COND nadd True).
Proof. exact (MK_COMB (@lem1310318) (@lem1310317 x h1)). Qed.
Lemma lem1310320 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem1310321 (x : nadd) (h1 : term25 x) : (term171 x) = term172.
Proof. exact (MK_COMB (@lem1310319 x h1) (@lem1310320)). Qed.
Lemma lem1310322 (x : nadd) : (term173 x) = (term173 x).
Proof. exact (eq_refl (term173 x)). Qed.
Lemma lem1310323 (x : nadd) (h1 : term25 x) : (term169 x) = (term174 x).
Proof. exact (MK_COMB (@lem1310321 x h1) (@lem1310322 x)). Qed.
Lemma lem1310325 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1310326 (t2 : nadd) (t1 : nadd) : (@COND nadd True t1 t2) = t1.
Proof. exact (@lem1310325 nadd t2 t1). Qed.
Lemma lem1310327 (x : nadd) : (term174 x) = term162.
Proof. exact (@lem1310326 (term173 x) term162). Qed.
Lemma lem1310328 (x : nadd) (h1 : term25 x) : (term169 x) = term162.
Proof. exact (TRANS (@lem1310323 x h1) (@lem1310327 x)). Qed.
Lemma lem1310329 (x : nadd) (h1 : term25 x) : (nadd_inv x) = term162.
Proof. exact (TRANS (@lem1310315 x) (@lem1310328 x h1)). Qed.
Lemma lem1310330 : nadd_eq = nadd_eq.
Proof. exact (eq_refl nadd_eq). Qed.
Lemma lem1310331 (x : nadd) (h1 : term25 x) : (term175 x) = term176.
Proof. exact (MK_COMB (@lem1310330) (@lem1310329 x h1)). Qed.
Lemma lem1310333 (x : nadd) : (nadd_inv x) = (term169 x).
Proof. exact (EQ_MP (@lem1310304 x) (@lem1310303 x)). Qed.
Lemma lem1310334 (y : nadd) : (nadd_inv y) = (term169 y).
Proof. exact (@lem1310333 y). Qed.
Lemma lem1310336 (y : nadd) (h1 : term25 y) : (term25 y) = True.
Proof. exact (EQ_MP (@lem1310310 y) (@lem1309211 y h1)). Qed.
Lemma lem1310337 : (@COND nadd) = (@COND nadd).
Proof. exact (eq_refl (@COND nadd)). Qed.
Lemma lem1310338 (y : nadd) (h1 : term25 y) : (term170 y) = (@COND nadd True).
Proof. exact (MK_COMB (@lem1310337) (@lem1310336 y h1)). Qed.
Lemma lem1310339 : term162 = term162.
Proof. exact (eq_refl term162). Qed.
Lemma lem1310340 (y : nadd) (h1 : term25 y) : (term171 y) = term172.
Proof. exact (MK_COMB (@lem1310338 y h1) (@lem1310339)). Qed.
Lemma lem1310341 (y : nadd) : (term173 y) = (term173 y).
Proof. exact (eq_refl (term173 y)). Qed.
Lemma lem1310342 (y : nadd) (h1 : term25 y) : (term169 y) = (term174 y).
Proof. exact (MK_COMB (@lem1310340 y h1) (@lem1310341 y)). Qed.
Lemma lem1310344 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1310345 (t2 : nadd) (t1 : nadd) : (@COND nadd True t1 t2) = t1.
Proof. exact (@lem1310344 nadd t2 t1). Qed.
Lemma lem1310346 (y : nadd) : (term174 y) = term162.
Proof. exact (@lem1310345 (term173 y) term162). Qed.
Lemma lem1310347 (y : nadd) (h1 : term25 y) : (term169 y) = term162.
Proof. exact (TRANS (@lem1310342 y h1) (@lem1310346 y)). Qed.
Lemma lem1310348 (y : nadd) (h1 : term25 y) : (nadd_inv y) = term162.
Proof. exact (TRANS (@lem1310334 y) (@lem1310347 y h1)). Qed.
Lemma lem1310349 (x : nadd) (y : nadd) (h1 : term25 x) (h2 : term25 y) : (term177 x y) = term178.
Proof. exact (MK_COMB (@lem1310331 x h1) (@lem1310348 y h2)). Qed.
Lemma lem1310351 (x : nadd) : (nadd_eq x x) = True.
Proof. exact (EQ_MP (@lem1310301 x) (@lem1310300 x)). Qed.
Lemma lem1310352 : term178 = True.
Proof. exact (@lem1310351 term162). Qed.
Lemma lem1310353 (x : nadd) (y : nadd) (h1 : term25 x) (h2 : term25 y) : (term177 x y) = True.
Proof. exact (TRANS (@lem1310349 x y h1 h2) (@lem1310352)). Qed.
Lemma lem1310354 (x : nadd) (y : nadd) (h1 : term25 x) (h2 : term25 y) : True = (term177 x y).
Proof. exact (SYM (@lem1310353 x y h1 h2)). Qed.
Lemma lem1310355 (x : nadd) (y : nadd) (h1 : term25 x) (h2 : term25 y) : term177 x y.
Proof. exact (EQ_MP (@lem1310354 x y h1 h2) (@lem0)). Qed.
Lemma lem1310356 (x : nadd) (y : nadd) (h1 : term25 x) (h2 : term25 y) : (term25 y) = (term177 x y).
Proof. exact (prop_ext (fun h3 : term25 y => @lem1310355 x y h1 h2) (fun h3 : term177 x y => @lem1309211 y h2)). Qed.
Lemma lem1310357 (x : nadd) (y : nadd) (h1 : term25 x) (h2 : term25 y) : term177 x y.
Proof. exact (EQ_MP (@lem1310356 x y h1 h2) (@lem1309211 y h2)). Qed.
Lemma lem1310358 (y : nadd) (x : nadd) (h1 : nadd_eq x y) (h2 : term25 x) : (term25 y) = (term177 x y).
Proof. exact (prop_ext (fun h3 : term25 y => @lem1310357 x y h2 h3) (fun h3 : term177 x y => @lem1310297 y x h1 h2)). Qed.
Lemma lem1310359 (y : nadd) (x : nadd) (h1 : nadd_eq x y) (h2 : term25 x) : term177 x y.
Proof. exact (EQ_MP (@lem1310358 y x h1 h2) (@lem1310297 y x h1 h2)). Qed.
Lemma lem1310360 (y : nadd) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1310361 (y : nadd) (h1 : term25 y) : term25 y.
Proof. exact (h1). Qed.
Lemma lem1310364 (x : nadd) (y : nadd) (h1 : term179 x y) : term179 x y.
Proof. exact (h1). Qed.
Lemma lem1310365 (x : nadd) (y : nadd) : term180 x y.
Proof. exact (fun h0 : term179 x y => @lem1310364 x y h0). Qed.
Lemma lem1310366 (x : nadd) (y : nadd) (h1 : term180 x y) : term180 x y.
Proof. exact (h1). Qed.
Lemma lem1310367 (x : nadd) (y : nadd) (h1 : term179 x y) : term179 x y.
Proof. exact (h1). Qed.
Lemma lem1310368 (x : nadd) (y : nadd) (h1 : term180 x y) (h2 : term179 x y) : term179 x y.
Proof. exact (@lem1310366 x y h1 (@lem1310367 x y h2)). Qed.
Lemma lem1310369 (x : nadd) (y : nadd) (h1 : term179 x y) : term181 x y.
Proof. exact (fun h0 : term180 x y => @lem1310368 x y h0 h1). Qed.
Lemma lem1310370 (x : nadd) (y : nadd) (h1 : term180 x y) : term180 x y.
Proof. exact (h1). Qed.
Lemma lem1310371 (x : nadd) (y : nadd) (h1 : term180 x y) (h2 : term179 x y) : term179 x y.
Proof. exact (@lem1310369 x y h2 (@lem1310370 x y h1)). Qed.
Lemma lem1310372 (x : nadd) (y : nadd) (h1 : term180 x y) : term180 x y.
Proof. exact (fun h0 : term179 x y => @lem1310371 x y h1 h0). Qed.
Lemma lem1310373 (x : nadd) (y : nadd) : term182 x y.
Proof. exact (fun h0 : term180 x y => @lem1310372 x y h0). Qed.
Lemma lem1310376 (x : nadd) (y : nadd) : term180 x y.
Proof. exact (@lem1310373 x y (@lem1310365 x y)). Qed.
Lemma lem1310402 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1310403 : term34 = term35.
Proof. exact (@lem1310402 term7). Qed.
Lemma lem1310420 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1310421 : term37 = term38.
Proof. exact (MK_COMB (@lem1310420) (@lem1310403)). Qed.
Lemma lem1310424 (y : nadd) : (term42 y) = (term42 y).
Proof. exact (eq_refl (term42 y)). Qed.
Lemma lem1310425 (y : nadd) : (term183 y) = (term184 y).
Proof. exact (MK_COMB (@lem1310424 y) (@lem1310421)). Qed.
Lemma lem1310428 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1310429 (x : nadd) (y : nadd) : (term185 x y) = (term186 x y).
Proof. exact (MK_COMB (@lem1310428 x) (@lem1310425 y)). Qed.
Lemma lem1310432 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1310433 (x : nadd) (y : nadd) : (term179 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1310432 x y) (@lem1310429 x y)). Qed.
Lemma lem1310436 (y : nadd) : (term188 y) = (term189 y).
Proof. exact (fun_ext (fun x : nadd => @lem1310433 x y)). Qed.
Lemma lem1310437 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1310438 (y : nadd) : (term190 y) = (term191 y).
Proof. exact (MK_COMB (@lem1310437) (@lem1310436 y)). Qed.
Lemma lem1310443 : term192 = term193.
Proof. exact (fun_ext (fun y : nadd => @lem1310438 y)). Qed.
Lemma lem1310444 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1310453 : term194 = term195.
Proof. exact (MK_COMB (@lem1310444) (@lem1310443)). Qed.
Lemma lem1310462 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term13 y x z).
Proof. exact (eq_refl (term13 y x z)). Qed.
Lemma lem1310463 (y : nadd) (x : nadd) : (term55 y x) = (term55 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1310462 y x z)). Qed.
Lemma lem1310464 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1310465 (y : nadd) (x : nadd) : (term11 y x) = (term11 y x).
Proof. exact (MK_COMB (@lem1310464) (@lem1310463 y x)). Qed.
Lemma lem1310466 (x : nadd) : (term56 x) = (term56 x).
Proof. exact (fun_ext (fun y : nadd => @lem1310465 y x)). Qed.
Lemma lem1310467 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1310468 (x : nadd) : (term9 x) = (term9 x).
Proof. exact (MK_COMB (@lem1310467) (@lem1310466 x)). Qed.
Lemma lem1310469 : term57 = term57.
Proof. exact (fun_ext (fun x : nadd => @lem1310468 x)). Qed.
Lemma lem1310470 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1310471 : term7 = term7.
Proof. exact (MK_COMB (@lem1310470) (@lem1310469)). Qed.
Lemma lem1310472 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1310473 : term35 = term35.
Proof. exact (MK_COMB (@lem1310472) (@lem1310471)). Qed.
Lemma lem1310478 (y : nadd) (x : nadd) : ((nadd_eq x y) = (nadd_eq y x)) = ((nadd_eq x y) = (nadd_eq y x)).
Proof. exact (eq_refl ((nadd_eq x y) = (nadd_eq y x))). Qed.
Lemma lem1310479 (x : nadd) : (term58 x) = (term58 x).
Proof. exact (fun_ext (fun y : nadd => @lem1310478 y x)). Qed.
Lemma lem1310480 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1310481 (x : nadd) : (term59 x) = (term59 x).
Proof. exact (MK_COMB (@lem1310480) (@lem1310479 x)). Qed.
Lemma lem1310482 : term60 = term60.
Proof. exact (fun_ext (fun x : nadd => @lem1310481 x)). Qed.
Lemma lem1310483 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1310484 : term61 = term61.
Proof. exact (MK_COMB (@lem1310483) (@lem1310482)). Qed.
Lemma lem1310485 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1310486 : term36 = term36.
Proof. exact (MK_COMB (@lem1310485) (@lem1310484)). Qed.
Lemma lem1310487 : term38 = term38.
Proof. exact (MK_COMB (@lem1310486) (@lem1310473)). Qed.
Lemma lem1310490 (y : nadd) : (term42 y) = (term42 y).
Proof. exact (eq_refl (term42 y)). Qed.
Lemma lem1310491 (y : nadd) : (term184 y) = (term184 y).
Proof. exact (MK_COMB (@lem1310490 y) (@lem1310487)). Qed.
Lemma lem1310496 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1310497 (x : nadd) (y : nadd) : (term186 x y) = (term186 x y).
Proof. exact (MK_COMB (@lem1310496 x) (@lem1310491 y)). Qed.
Lemma lem1310500 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1310501 (x : nadd) (y : nadd) : (term187 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1310500 x y) (@lem1310497 x y)). Qed.
Lemma lem1310502 (y : nadd) : (term189 y) = (term189 y).
Proof. exact (fun_ext (fun x : nadd => @lem1310501 x y)). Qed.
Lemma lem1310503 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1310504 (y : nadd) : (term191 y) = (term191 y).
Proof. exact (MK_COMB (@lem1310503) (@lem1310502 y)). Qed.
Lemma lem1310505 : term193 = term193.
Proof. exact (fun_ext (fun y : nadd => @lem1310504 y)). Qed.
Lemma lem1310506 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1310507 : term195 = term195.
Proof. exact (MK_COMB (@lem1310506) (@lem1310505)). Qed.
Lemma lem1310564 : term194 = term195.
Proof. exact (TRANS (@lem1310453) (@lem1310507)). Qed.
Lemma lem1310565 : term195 = term194.
Proof. exact (SYM (@lem1310564)). Qed.
Lemma lem1310570 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1310576 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1310582 (x : nadd) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1310588 (y : nadd) (h1 : term25 y) : term25 y.
Proof. exact (h1). Qed.
Lemma lem1310882 (x : nadd) (y : nadd) (z : nadd) : (term116 x y z) = (term117 x y z).
Proof. exact (@lem17045 (nadd_eq x y) (nadd_eq y z)). Qed.
Lemma lem1310883 (x : nadd) (z : nadd) : (nadd_eq x z) = (nadd_eq x z).
Proof. exact (eq_refl (nadd_eq x z)). Qed.
Lemma lem1310884 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1310885 (x : nadd) (y : nadd) (z : nadd) : (term118 x y z) = (term119 x y z).
Proof. exact (MK_COMB (@lem1310884) (@lem1310882 x y z)). Qed.
Lemma lem1310886 (y : nadd) (x : nadd) (z : nadd) : (term120 y x z) = (term121 y x z).
Proof. exact (MK_COMB (@lem1310885 x y z) (@lem1310883 x z)). Qed.
Lemma lem1310887 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term120 y x z).
Proof. exact (@lem17265 (term14 x y z) (nadd_eq x z)). Qed.
Lemma lem1310888 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term121 y x z).
Proof. exact (TRANS (@lem1310887 y x z) (@lem1310886 y x z)). Qed.
Lemma lem1310889 (y : nadd) (x : nadd) : (term55 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1310888 y x z)). Qed.
Lemma lem1310890 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1310891 (y : nadd) (x : nadd) : (term11 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1310890) (@lem1310889 y x)). Qed.
Lemma lem1310892 (x : nadd) : (term56 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1310891 y x)). Qed.
Lemma lem1310893 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1310894 (x : nadd) : (term9 x) = (term125 x).
Proof. exact (MK_COMB (@lem1310893) (@lem1310892 x)). Qed.
Lemma lem1310895 : term57 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1310894 x)). Qed.
Lemma lem1310896 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1310957 : term7 = term127.
Proof. exact (MK_COMB (@lem1310896) (@lem1310895)). Qed.
Lemma lem1310958 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1310957) (@lem1310570 h1)). Qed.
Lemma lem1310964 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1310976 (x : nadd) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1310986 (y : nadd) (h1 : term25 y) : term25 y.
Proof. exact (h1). Qed.
Lemma lem1311057 (y : nadd) (x : nadd) (z : nadd) : (term121 y x z) = (term121 y x z).
Proof. exact (eq_refl (term121 y x z)). Qed.
Lemma lem1311058 (y : nadd) (x : nadd) : (term122 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1311057 y x z)). Qed.
Lemma lem1311059 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311060 (y : nadd) (x : nadd) : (term123 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1311059) (@lem1311058 y x)). Qed.
Lemma lem1311061 (x : nadd) : (term124 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1311060 y x)). Qed.
Lemma lem1311062 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311063 (x : nadd) : (term125 x) = (term125 x).
Proof. exact (MK_COMB (@lem1311062) (@lem1311061 x)). Qed.
Lemma lem1311064 : term126 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1311063 x)). Qed.
Lemma lem1311065 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311066 : term127 = term127.
Proof. exact (MK_COMB (@lem1311065) (@lem1311064)). Qed.
Lemma lem1311067 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1311066) (@lem1310958 h1)). Qed.
Lemma lem1311073 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1311077 (x : nadd) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1311081 (y : nadd) (h1 : term25 y) : term25 y.
Proof. exact (h1). Qed.
Lemma lem1311095 (y : nadd) (x : nadd) (z : nadd) : (term121 y x z) = (term121 y x z).
Proof. exact (eq_refl (term121 y x z)). Qed.
Lemma lem1311096 (y : nadd) (x : nadd) : (term122 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1311095 y x z)). Qed.
Lemma lem1311097 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311098 (y : nadd) (x : nadd) : (term123 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1311097) (@lem1311096 y x)). Qed.
Lemma lem1311099 (x : nadd) : (term124 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1311098 y x)). Qed.
Lemma lem1311100 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311101 (x : nadd) : (term125 x) = (term125 x).
Proof. exact (MK_COMB (@lem1311100) (@lem1311099 x)). Qed.
Lemma lem1311102 : term126 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1311101 x)). Qed.
Lemma lem1311103 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311105 : term127 = term127.
Proof. exact (MK_COMB (@lem1311103) (@lem1311102)). Qed.
Lemma lem1311106 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1311105) (@lem1311067 h1)). Qed.
Lemma lem1311139 (_23361 : nadd) (h1 : term7) : term128 _23361.
Proof. exact (@lem1311106 h1 _23361). Qed.
Lemma lem1311140 (_23361 : nadd) : (term128 _23361) = (term125 _23361).
Proof. exact (eq_refl (term128 _23361)). Qed.
Lemma lem1311141 (_23361 : nadd) (h1 : term7) : term125 _23361.
Proof. exact (EQ_MP (@lem1311140 _23361) (@lem1311139 _23361 h1)). Qed.
Lemma lem1311142 (_23361 : nadd) (_23362 : nadd) (h1 : term7) : term129 _23361 _23362.
Proof. exact (@lem1311141 _23361 h1 _23362). Qed.
Lemma lem1311143 (_23362 : nadd) (_23361 : nadd) : (term129 _23361 _23362) = (term123 _23362 _23361).
Proof. exact (eq_refl (term129 _23361 _23362)). Qed.
Lemma lem1311144 (_23362 : nadd) (_23361 : nadd) (h1 : term7) : term123 _23362 _23361.
Proof. exact (EQ_MP (@lem1311143 _23362 _23361) (@lem1311142 _23361 _23362 h1)). Qed.
Lemma lem1311145 (_23362 : nadd) (_23361 : nadd) (_23363 : nadd) (h1 : term7) : term130 _23362 _23361 _23363.
Proof. exact (@lem1311144 _23362 _23361 h1 _23363). Qed.
Lemma lem1311146 (_23362 : nadd) (_23361 : nadd) (_23363 : nadd) : (term130 _23362 _23361 _23363) = (term121 _23362 _23361 _23363).
Proof. exact (eq_refl (term130 _23362 _23361 _23363)). Qed.
Lemma lem1311147 (_23362 : nadd) (_23361 : nadd) (_23363 : nadd) (h1 : term7) : term121 _23362 _23361 _23363.
Proof. exact (EQ_MP (@lem1311146 _23362 _23361 _23363) (@lem1311145 _23362 _23361 _23363 h1)). Qed.
Lemma lem1311161 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1311163 (x : nadd) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1311165 (y : nadd) (h1 : term25 y) : term25 y.
Proof. exact (h1). Qed.
Lemma lem1311176 (_23362 : nadd) (_23361 : nadd) (_23363 : nadd) : (term121 _23362 _23361 _23363) = (term131 _23362 _23361 _23363).
Proof. exact (@lem1309194 (term132 _23361 _23362) (term132 _23362 _23363) (nadd_eq _23361 _23363)). Qed.
Lemma lem1311177 (_23362 : nadd) (_23361 : nadd) (_23363 : nadd) (h1 : term7) : term131 _23362 _23361 _23363.
Proof. exact (EQ_MP (@lem1311176 _23362 _23361 _23363) (@lem1311147 _23362 _23361 _23363 h1)). Qed.
Lemma lem1311191 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1311192 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term133 x y.
Proof. exact (fun h0 : term132 x y => @lem1311191 x y h1). Qed.
Lemma lem1311194 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1311195 (x : nadd) (y : nadd) : (term133 x y) = (nadd_eq x y).
Proof. exact (@lem1311194 (nadd_eq x y)). Qed.
Lemma lem1311196 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (EQ_MP (@lem1311195 x y) (@lem1311192 x y h1)). Qed.
Lemma lem1311198 (y : nadd) (h1 : term25 y) : term25 y.
Proof. exact (h1). Qed.
Lemma lem1311199 (y : nadd) (h1 : term25 y) : term143 y.
Proof. exact (fun h0 : term27 y => @lem1311198 y h1). Qed.
Lemma lem1311201 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1311202 (y : nadd) : (term143 y) = (term25 y).
Proof. exact (@lem1311201 (term25 y)). Qed.
Lemma lem1311203 (y : nadd) (h1 : term25 y) : term25 y.
Proof. exact (EQ_MP (@lem1311202 y) (@lem1311199 y h1)). Qed.
Lemma lem1311219 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1311220 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : (term144 _23362 _23361 _23363) = (term145 _23361 _23362 _23363).
Proof. exact (@lem1311219 (nadd_eq _23361 _23363) (term132 _23362 _23363)). Qed.
Lemma lem1311226 (_23361 : nadd) (_23362 : nadd) : (term146 _23361 _23362) = (term146 _23361 _23362).
Proof. exact (eq_refl (term146 _23361 _23362)). Qed.
Lemma lem1311227 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : (term131 _23362 _23361 _23363) = (term147 _23361 _23362 _23363).
Proof. exact (MK_COMB (@lem1311226 _23361 _23362) (@lem1311220 _23361 _23362 _23363)). Qed.
Lemma lem1311231 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1311232 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : (term147 _23361 _23362 _23363) = (term148 _23361 _23362 _23363).
Proof. exact (@lem1311231 (nadd_eq _23361 _23363) (term132 _23361 _23362) (term132 _23362 _23363)). Qed.
Lemma lem1311248 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : (term131 _23362 _23361 _23363) = (term148 _23361 _23362 _23363).
Proof. exact (TRANS (@lem1311227 _23361 _23362 _23363) (@lem1311232 _23361 _23362 _23363)). Qed.
Lemma lem1311249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1311250 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : (term149 _23362 _23361 _23363) = (term150 _23361 _23362 _23363).
Proof. exact (MK_COMB (@lem1311249) (@lem1311248 _23361 _23362 _23363)). Qed.
Lemma lem1311266 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : (term148 _23361 _23362 _23363) = (term148 _23361 _23362 _23363).
Proof. exact (eq_refl (term148 _23361 _23362 _23363)). Qed.
Lemma lem1311267 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : ((term131 _23362 _23361 _23363) = (term148 _23361 _23362 _23363)) = ((term148 _23361 _23362 _23363) = (term148 _23361 _23362 _23363)).
Proof. exact (MK_COMB (@lem1311250 _23361 _23362 _23363) (@lem1311266 _23361 _23362 _23363)). Qed.
Lemma lem1311269 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1311270 (x : Prop) : (x = x) = True.
Proof. exact (@lem1311269 Prop x). Qed.
Lemma lem1311271 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : ((term148 _23361 _23362 _23363) = (term148 _23361 _23362 _23363)) = True.
Proof. exact (@lem1311270 (term148 _23361 _23362 _23363)). Qed.
Lemma lem1311272 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : ((term131 _23362 _23361 _23363) = (term148 _23361 _23362 _23363)) = True.
Proof. exact (TRANS (@lem1311267 _23361 _23362 _23363) (@lem1311271 _23361 _23362 _23363)). Qed.
Lemma lem1311273 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : True = ((term131 _23362 _23361 _23363) = (term148 _23361 _23362 _23363)).
Proof. exact (SYM (@lem1311272 _23361 _23362 _23363)). Qed.
Lemma lem1311274 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : (term131 _23362 _23361 _23363) = (term148 _23361 _23362 _23363).
Proof. exact (EQ_MP (@lem1311273 _23361 _23362 _23363) (@lem0)). Qed.
Lemma lem1311275 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) (h1 : term7) : term148 _23361 _23362 _23363.
Proof. exact (EQ_MP (@lem1311274 _23361 _23362 _23363) (@lem1311177 _23362 _23361 _23363 h1)). Qed.
Lemma lem1311277 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1311278 (_23362 : nadd) (_23361 : nadd) (_23363 : nadd) : (term148 _23361 _23362 _23363) = (term151 _23362 _23361 _23363).
Proof. exact (@lem1311277 (term117 _23361 _23362 _23363) (nadd_eq _23361 _23363)). Qed.
Lemma lem1311280 (a : Prop) (b : Prop) : (term152 a b) = (term153 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1311281 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : (term154 _23361 _23362 _23363) = (term155 _23361 _23362 _23363).
Proof. exact (@lem1311280 (term132 _23361 _23362) (term132 _23362 _23363)). Qed.
Lemma lem1311283 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1311284 (_23361 : nadd) (_23362 : nadd) : (term140 _23361 _23362) = (nadd_eq _23361 _23362).
Proof. exact (@lem1311283 (nadd_eq _23361 _23362)). Qed.
Lemma lem1311285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1311286 (_23361 : nadd) (_23362 : nadd) : (term156 _23361 _23362) = (term157 _23361 _23362).
Proof. exact (MK_COMB (@lem1311285) (@lem1311284 _23361 _23362)). Qed.
Lemma lem1311288 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1311289 (_23362 : nadd) (_23363 : nadd) : (term140 _23362 _23363) = (nadd_eq _23362 _23363).
Proof. exact (@lem1311288 (nadd_eq _23362 _23363)). Qed.
Lemma lem1311290 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : (term155 _23361 _23362 _23363) = (term14 _23361 _23362 _23363).
Proof. exact (MK_COMB (@lem1311286 _23361 _23362) (@lem1311289 _23362 _23363)). Qed.
Lemma lem1311291 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : (term154 _23361 _23362 _23363) = (term14 _23361 _23362 _23363).
Proof. exact (TRANS (@lem1311281 _23361 _23362 _23363) (@lem1311290 _23361 _23362 _23363)). Qed.
Lemma lem1311292 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1311293 (_23361 : nadd) (_23362 : nadd) (_23363 : nadd) : (term158 _23361 _23362 _23363) = (term159 _23361 _23362 _23363).
Proof. exact (MK_COMB (@lem1311292) (@lem1311291 _23361 _23362 _23363)). Qed.
Lemma lem1311294 (_23361 : nadd) (_23363 : nadd) : (nadd_eq _23361 _23363) = (nadd_eq _23361 _23363).
Proof. exact (eq_refl (nadd_eq _23361 _23363)). Qed.
Lemma lem1311295 (_23362 : nadd) (_23361 : nadd) (_23363 : nadd) : (term151 _23362 _23361 _23363) = (term13 _23362 _23361 _23363).
Proof. exact (MK_COMB (@lem1311293 _23361 _23362 _23363) (@lem1311294 _23361 _23363)). Qed.
Lemma lem1311296 (_23362 : nadd) (_23361 : nadd) (_23363 : nadd) : (term148 _23361 _23362 _23363) = (term13 _23362 _23361 _23363).
Proof. exact (TRANS (@lem1311278 _23362 _23361 _23363) (@lem1311295 _23362 _23361 _23363)). Qed.
Lemma lem1311298 (x : nadd) (y : nadd) (h1 : nadd_eq x y) (h2 : term25 y) : term160 x y.
Proof. exact (conj (@lem1311196 x y h1) (@lem1311203 y h2)). Qed.
Lemma lem1311300 (_23362 : nadd) (_23361 : nadd) (_23363 : nadd) (h1 : term7) : term13 _23362 _23361 _23363.
Proof. exact (EQ_MP (@lem1311296 _23362 _23361 _23363) (@lem1311275 _23361 _23362 _23363 h1)). Qed.
Lemma lem1311301 (y : nadd) (x : nadd) (h1 : term7) : term161 y x.
Proof. exact (@lem1311300 y x term162 h1). Qed.
Lemma lem1311304 (x : nadd) (y : nadd) (h1 : term7) (h2 : nadd_eq x y) (h3 : term25 y) : term25 x.
Proof. exact (@lem1311301 y x h1 (@lem1311298 x y h2 h3)). Qed.
Lemma lem1311305 (x : nadd) (y : nadd) (h1 : term7) (h2 : nadd_eq x y) (h3 : term25 y) : term143 x.
Proof. exact (fun h0 : term27 x => @lem1311304 x y h1 h2 h3). Qed.
Lemma lem1311307 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1311308 (x : nadd) : (term143 x) = (term25 x).
Proof. exact (@lem1311307 (term25 x)). Qed.
Lemma lem1311309 (x : nadd) (y : nadd) (h1 : term7) (h2 : nadd_eq x y) (h3 : term25 y) : term25 x.
Proof. exact (EQ_MP (@lem1311308 x) (@lem1311305 x y h1 h2 h3)). Qed.
Lemma lem1311312 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1311314 (x : nadd) : (term27 x) = (term163 x).
Proof. exact (@lem1311312 (term25 x)). Qed.
Lemma lem1311317 (x : nadd) (h1 : term27 x) : term163 x.
Proof. exact (EQ_MP (@lem1311314 x) (@lem1311163 x h1)). Qed.
Lemma lem1311320 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (@lem1311317 x h2 (@lem1311309 x y h1 h3 h4)). Qed.
Lemma lem1311321 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : term164.
Proof. exact (fun h0 : ~ False => @lem1311320 x y h1 h2 h3 h4). Qed.
Lemma lem1311323 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1311324 : term164 = False.
Proof. exact (@lem1311323 False). Qed.
Lemma lem1311325 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311324) (@lem1311321 x y h1 h2 h3 h4)). Qed.
Lemma lem1311326 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (term25 y) = False.
Proof. exact (prop_ext (fun h5 : term25 y => @lem1311325 x y h1 h2 h3 h4) (fun h5 : False => @lem1311165 y h4)). Qed.
Lemma lem1311327 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311326 x y h1 h2 h3 h4) (@lem1311165 y h4)). Qed.
Lemma lem1311328 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (term27 x) = False.
Proof. exact (prop_ext (fun h5 : term27 x => @lem1311327 x y h1 h2 h3 h4) (fun h5 : False => @lem1311163 x h2)). Qed.
Lemma lem1311329 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311328 x y h1 h2 h3 h4) (@lem1311163 x h2)). Qed.
Lemma lem1311330 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h5 : nadd_eq x y => @lem1311329 x y h1 h2 h3 h4) (fun h5 : False => @lem1311161 x y h3)). Qed.
Lemma lem1311331 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311330 x y h1 h2 h3 h4) (@lem1311161 x y h3)). Qed.
Lemma lem1311332 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (term25 y) = False.
Proof. exact (prop_ext (fun h5 : term25 y => @lem1311331 x y h1 h2 h3 h4) (fun h5 : False => @lem1311081 y h4)). Qed.
Lemma lem1311333 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311332 x y h1 h2 h3 h4) (@lem1311081 y h4)). Qed.
Lemma lem1311334 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (term27 x) = False.
Proof. exact (prop_ext (fun h5 : term27 x => @lem1311333 x y h1 h2 h3 h4) (fun h5 : False => @lem1311077 x h2)). Qed.
Lemma lem1311335 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311334 x y h1 h2 h3 h4) (@lem1311077 x h2)). Qed.
Lemma lem1311336 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h5 : nadd_eq x y => @lem1311335 x y h1 h2 h3 h4) (fun h5 : False => @lem1311073 x y h3)). Qed.
Lemma lem1311337 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311336 x y h1 h2 h3 h4) (@lem1311073 x y h3)). Qed.
Lemma lem1311338 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (term25 y) = False.
Proof. exact (prop_ext (fun h5 : term25 y => @lem1311337 x y h1 h2 h3 h4) (fun h5 : False => @lem1311081 y h4)). Qed.
Lemma lem1311339 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311338 x y h1 h2 h3 h4) (@lem1311081 y h4)). Qed.
Lemma lem1311340 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (term27 x) = False.
Proof. exact (prop_ext (fun h5 : term27 x => @lem1311339 x y h1 h2 h3 h4) (fun h5 : False => @lem1311077 x h2)). Qed.
Lemma lem1311341 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311340 x y h1 h2 h3 h4) (@lem1311077 x h2)). Qed.
Lemma lem1311342 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h5 : nadd_eq x y => @lem1311341 x y h1 h2 h3 h4) (fun h5 : False => @lem1311073 x y h3)). Qed.
Lemma lem1311343 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311342 x y h1 h2 h3 h4) (@lem1311073 x y h3)). Qed.
Lemma lem1311344 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (term25 y) = False.
Proof. exact (prop_ext (fun h5 : term25 y => @lem1311343 x y h1 h2 h3 h4) (fun h5 : False => @lem1310986 y h4)). Qed.
Lemma lem1311345 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311344 x y h1 h2 h3 h4) (@lem1310986 y h4)). Qed.
Lemma lem1311346 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (term27 x) = False.
Proof. exact (prop_ext (fun h5 : term27 x => @lem1311345 x y h1 h2 h3 h4) (fun h5 : False => @lem1310976 x h2)). Qed.
Lemma lem1311347 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311346 x y h1 h2 h3 h4) (@lem1310976 x h2)). Qed.
Lemma lem1311348 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h5 : nadd_eq x y => @lem1311347 x y h1 h2 h3 h4) (fun h5 : False => @lem1310964 x y h3)). Qed.
Lemma lem1311349 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311348 x y h1 h2 h3 h4) (@lem1310964 x y h3)). Qed.
Lemma lem1311350 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (term25 y) = False.
Proof. exact (prop_ext (fun h5 : term25 y => @lem1311349 x y h1 h2 h3 h4) (fun h5 : False => @lem1310588 y h4)). Qed.
Lemma lem1311351 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311350 x y h1 h2 h3 h4) (@lem1310588 y h4)). Qed.
Lemma lem1311352 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (term27 x) = False.
Proof. exact (prop_ext (fun h5 : term27 x => @lem1311351 x y h1 h2 h3 h4) (fun h5 : False => @lem1310582 x h2)). Qed.
Lemma lem1311353 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311352 x y h1 h2 h3 h4) (@lem1310582 x h2)). Qed.
Lemma lem1311354 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h5 : nadd_eq x y => @lem1311353 x y h1 h2 h3 h4) (fun h5 : False => @lem1310576 x y h3)). Qed.
Lemma lem1311355 (x : nadd) (y : nadd) (h1 : term7) (h2 : term27 x) (h3 : nadd_eq x y) (h4 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311354 x y h1 h2 h3 h4) (@lem1310576 x y h3)). Qed.
Lemma lem1311356 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) (h3 : term25 y) : term34.
Proof. exact (fun h0 : term7 => @lem1311355 x y h0 h1 h2 h3). Qed.
Lemma lem1311357 : term34 = term35.
Proof. exact (@lem69 term7). Qed.
Lemma lem1311358 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) (h3 : term25 y) : term35.
Proof. exact (EQ_MP (@lem1311357) (@lem1311356 x y h1 h2 h3)). Qed.
Lemma lem1311359 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) (h3 : term25 y) : term38.
Proof. exact (fun h0 : term61 => @lem1311358 x y h1 h2 h3). Qed.
Lemma lem1311360 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) : term184 y.
Proof. exact (fun h0 : term25 y => @lem1311359 x y h1 h2 h0). Qed.
Lemma lem1311361 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term186 x y.
Proof. exact (fun h0 : term27 x => @lem1311360 x y h0 h1). Qed.
Lemma lem1311362 (x : nadd) (y : nadd) : term187 x y.
Proof. exact (fun h0 : nadd_eq x y => @lem1311361 x y h0). Qed.
Lemma lem1311367 (y : nadd) : term191 y.
Proof. exact (fun x : nadd => @lem1311362 x y). Qed.
Lemma lem1311372 : term195.
Proof. exact (fun y : nadd => @lem1311367 y). Qed.
Lemma lem1311373 : term194.
Proof. exact (EQ_MP (@lem1310565) (@lem1311372)). Qed.
Lemma lem1311374 (y : nadd) : term196 y.
Proof. exact (@lem1311373 y). Qed.
Lemma lem1311375 (y : nadd) : (term196 y) = (term190 y).
Proof. exact (eq_refl (term196 y)). Qed.
Lemma lem1311376 (y : nadd) : term190 y.
Proof. exact (EQ_MP (@lem1311375 y) (@lem1311374 y)). Qed.
Lemma lem1311377 (y : nadd) (x : nadd) : term197 y x.
Proof. exact (@lem1311376 y x). Qed.
Lemma lem1311378 (x : nadd) (y : nadd) : (term197 y x) = (term179 x y).
Proof. exact (eq_refl (term197 y x)). Qed.
Lemma lem1311379 (x : nadd) (y : nadd) : term179 x y.
Proof. exact (EQ_MP (@lem1311378 x y) (@lem1311377 y x)). Qed.
Lemma lem1311381 (x : nadd) (y : nadd) : term179 x y.
Proof. exact (@lem1310376 x y (@lem1311379 x y)). Qed.
Lemma lem1311382 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term185 x y.
Proof. exact (@lem1311381 x y (@lem1309210 x y h1)). Qed.
Lemma lem1311383 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) : term183 y.
Proof. exact (@lem1311382 x y h2 (@lem1309209 x h1)). Qed.
Lemma lem1311384 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) (h3 : term25 y) : term37.
Proof. exact (@lem1311383 x y h1 h2 (@lem1310361 y h3)). Qed.
Lemma lem1311385 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) (h3 : term25 y) : term34.
Proof. exact (@lem1311384 x y h1 h2 h3 (@lem1268060)). Qed.
Lemma lem1311386 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) (h3 : term25 y) : False.
Proof. exact (@lem1311385 x y h1 h2 h3 (@lem1268295)). Qed.
Lemma lem1311387 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) (h3 : term25 y) : (term25 y) = False.
Proof. exact (prop_ext (fun h4 : term25 y => @lem1311386 x y h1 h2 h3) (fun h4 : False => @lem1310361 y h3)). Qed.
Lemma lem1311388 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) (h3 : term25 y) : False.
Proof. exact (EQ_MP (@lem1311387 x y h1 h2 h3) (@lem1310361 y h3)). Qed.
Lemma lem1311389 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) : term163 y.
Proof. exact (fun h0 : term25 y => @lem1311388 x y h1 h2 h0). Qed.
Lemma lem1311390 (y : nadd) : (term163 y) = (term27 y).
Proof. exact (@lem69 (term25 y)). Qed.
Lemma lem1311391 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) : term27 y.
Proof. exact (EQ_MP (@lem1311390 y) (@lem1311389 x y h1 h2)). Qed.
Lemma lem1311393 (x : nadd) (z : nadd) : term18 x z.
Proof. exact (EQ_MP (@lem1309183 x z) (@lem1309182 x z)). Qed.
Lemma lem1311394 (x : nadd) (y : nadd) : term198 x y.
Proof. exact (@lem1311393 (nadd_inv x) (nadd_inv y)). Qed.
Lemma lem1311396 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1311397 (y : nadd) : (term199 y) = (term200 y).
Proof. exact (@lem1311396 (term199 y)). Qed.
Lemma lem1311398 (y : nadd) : (term200 y) = (term199 y).
Proof. exact (SYM (@lem1311397 y)). Qed.
Lemma lem1311399 (y : nadd) (h1 : term201 y) : term201 y.
Proof. exact (h1). Qed.
Lemma lem1311402 (x : nadd) (y : nadd) (h1 : term202 x y) : term202 x y.
Proof. exact (h1). Qed.
Lemma lem1311403 (x : nadd) (y : nadd) : term203 x y.
Proof. exact (fun h0 : term202 x y => @lem1311402 x y h0). Qed.
Lemma lem1311404 (x : nadd) (y : nadd) (h1 : term203 x y) : term203 x y.
Proof. exact (h1). Qed.
Lemma lem1311405 (x : nadd) (y : nadd) (h1 : term202 x y) : term202 x y.
Proof. exact (h1). Qed.
Lemma lem1311406 (x : nadd) (y : nadd) (h1 : term203 x y) (h2 : term202 x y) : term202 x y.
Proof. exact (@lem1311404 x y h1 (@lem1311405 x y h2)). Qed.
Lemma lem1311407 (x : nadd) (y : nadd) (h1 : term202 x y) : term204 x y.
Proof. exact (fun h0 : term203 x y => @lem1311406 x y h0 h1). Qed.
Lemma lem1311408 (x : nadd) (y : nadd) (h1 : term203 x y) : term203 x y.
Proof. exact (h1). Qed.
Lemma lem1311409 (x : nadd) (y : nadd) (h1 : term203 x y) (h2 : term202 x y) : term202 x y.
Proof. exact (@lem1311407 x y h2 (@lem1311408 x y h1)). Qed.
Lemma lem1311410 (x : nadd) (y : nadd) (h1 : term203 x y) : term203 x y.
Proof. exact (fun h0 : term202 x y => @lem1311409 x y h1 h0). Qed.
Lemma lem1311411 (x : nadd) (y : nadd) : term205 x y.
Proof. exact (fun h0 : term203 x y => @lem1311410 x y h0). Qed.
Lemma lem1311414 (x : nadd) (y : nadd) : term203 x y.
Proof. exact (@lem1311411 x y (@lem1311403 x y)). Qed.
Lemma lem1311456 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1311457 : term206 = term207.
Proof. exact (@lem1311456 term208). Qed.
Lemma lem1311466 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem1311467 : term210 = term211.
Proof. exact (MK_COMB (@lem1311466) (@lem1311457)). Qed.
Lemma lem1311470 : term212 = term212.
Proof. exact (eq_refl term212). Qed.
Lemma lem1311471 : term213 = term214.
Proof. exact (MK_COMB (@lem1311470) (@lem1311467)). Qed.
Lemma lem1311474 (y : nadd) : (term215 y) = (term215 y).
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem1311475 (y : nadd) : (term216 y) = (term217 y).
Proof. exact (MK_COMB (@lem1311474 y) (@lem1311471)). Qed.
Lemma lem1311478 (y : nadd) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem1311479 (y : nadd) : (term218 y) = (term219 y).
Proof. exact (MK_COMB (@lem1311478 y) (@lem1311475 y)). Qed.
Lemma lem1311482 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1311483 (x : nadd) (y : nadd) : (term220 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem1311482 x) (@lem1311479 y)). Qed.
Lemma lem1311486 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1311487 (x : nadd) (y : nadd) : (term202 x y) = (term222 x y).
Proof. exact (MK_COMB (@lem1311486 x y) (@lem1311483 x y)). Qed.
Lemma lem1311490 (y : nadd) : (term223 y) = (term224 y).
Proof. exact (fun_ext (fun x : nadd => @lem1311487 x y)). Qed.
Lemma lem1311491 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311492 (y : nadd) : (term225 y) = (term226 y).
Proof. exact (MK_COMB (@lem1311491) (@lem1311490 y)). Qed.
Lemma lem1311497 : term227 = term228.
Proof. exact (fun_ext (fun y : nadd => @lem1311492 y)). Qed.
Lemma lem1311498 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311507 : term229 = term230.
Proof. exact (MK_COMB (@lem1311498) (@lem1311497)). Qed.
Lemma lem1311508 (y : nadd) (x : nadd) : (term231 y x) = (term231 y x).
Proof. exact (eq_refl (term231 y x)). Qed.
Lemma lem1311509 (x : nadd) : (term232 x) = (term232 x).
Proof. exact (fun_ext (fun y : nadd => @lem1311508 y x)). Qed.
Lemma lem1311510 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311511 (x : nadd) : (term233 x) = (term233 x).
Proof. exact (MK_COMB (@lem1311510) (@lem1311509 x)). Qed.
Lemma lem1311512 : term234 = term234.
Proof. exact (fun_ext (fun x : nadd => @lem1311511 x)). Qed.
Lemma lem1311513 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311514 : term208 = term208.
Proof. exact (MK_COMB (@lem1311513) (@lem1311512)). Qed.
Lemma lem1311515 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1311516 : term207 = term207.
Proof. exact (MK_COMB (@lem1311515) (@lem1311514)). Qed.
Lemma lem1311517 (x : nadd) : (term235 x) = (term235 x).
Proof. exact (eq_refl (term235 x)). Qed.
Lemma lem1311518 : term236 = term236.
Proof. exact (fun_ext (fun x : nadd => @lem1311517 x)). Qed.
Lemma lem1311519 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311520 : term237 = term237.
Proof. exact (MK_COMB (@lem1311519) (@lem1311518)). Qed.
Lemma lem1311521 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1311522 : term209 = term209.
Proof. exact (MK_COMB (@lem1311521) (@lem1311520)). Qed.
Lemma lem1311523 : term211 = term211.
Proof. exact (MK_COMB (@lem1311522) (@lem1311516)). Qed.
Lemma lem1311532 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term13 y x z).
Proof. exact (eq_refl (term13 y x z)). Qed.
Lemma lem1311533 (y : nadd) (x : nadd) : (term55 y x) = (term55 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1311532 y x z)). Qed.
Lemma lem1311534 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311535 (y : nadd) (x : nadd) : (term11 y x) = (term11 y x).
Proof. exact (MK_COMB (@lem1311534) (@lem1311533 y x)). Qed.
Lemma lem1311536 (x : nadd) : (term56 x) = (term56 x).
Proof. exact (fun_ext (fun y : nadd => @lem1311535 y x)). Qed.
Lemma lem1311537 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311538 (x : nadd) : (term9 x) = (term9 x).
Proof. exact (MK_COMB (@lem1311537) (@lem1311536 x)). Qed.
Lemma lem1311539 : term57 = term57.
Proof. exact (fun_ext (fun x : nadd => @lem1311538 x)). Qed.
Lemma lem1311540 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311541 : term7 = term7.
Proof. exact (MK_COMB (@lem1311540) (@lem1311539)). Qed.
Lemma lem1311542 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1311543 : term212 = term212.
Proof. exact (MK_COMB (@lem1311542) (@lem1311541)). Qed.
Lemma lem1311544 : term214 = term214.
Proof. exact (MK_COMB (@lem1311543) (@lem1311523)). Qed.
Lemma lem1311549 (y : nadd) : (term215 y) = (term215 y).
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem1311550 (y : nadd) : (term217 y) = (term217 y).
Proof. exact (MK_COMB (@lem1311549 y) (@lem1311544)). Qed.
Lemma lem1311555 (y : nadd) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem1311556 (y : nadd) : (term219 y) = (term219 y).
Proof. exact (MK_COMB (@lem1311555 y) (@lem1311550 y)). Qed.
Lemma lem1311561 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1311562 (x : nadd) (y : nadd) : (term221 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem1311561 x) (@lem1311556 y)). Qed.
Lemma lem1311565 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1311566 (x : nadd) (y : nadd) : (term222 x y) = (term222 x y).
Proof. exact (MK_COMB (@lem1311565 x y) (@lem1311562 x y)). Qed.
Lemma lem1311567 (y : nadd) : (term224 y) = (term224 y).
Proof. exact (fun_ext (fun x : nadd => @lem1311566 x y)). Qed.
Lemma lem1311568 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311569 (y : nadd) : (term226 y) = (term226 y).
Proof. exact (MK_COMB (@lem1311568) (@lem1311567 y)). Qed.
Lemma lem1311570 : term228 = term228.
Proof. exact (fun_ext (fun y : nadd => @lem1311569 y)). Qed.
Lemma lem1311571 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311572 : term230 = term230.
Proof. exact (MK_COMB (@lem1311571) (@lem1311570)). Qed.
Lemma lem1311639 : term229 = term230.
Proof. exact (TRANS (@lem1311507) (@lem1311572)). Qed.
Lemma lem1311640 : term230 = term229.
Proof. exact (SYM (@lem1311639)). Qed.
Lemma lem1311645 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1311646 (h1 : term237) : term237.
Proof. exact (h1). Qed.
Lemma lem1311647 (h1 : term208) : term208.
Proof. exact (h1). Qed.
Lemma lem1311671 (y : nadd) (h1 : term201 y) : term201 y.
Proof. exact (h1). Qed.
Lemma lem1311678 (x : nadd) (y : nadd) (z : nadd) : (term116 x y z) = (term117 x y z).
Proof. exact (@lem17045 (nadd_eq x y) (nadd_eq y z)). Qed.
Lemma lem1311679 (x : nadd) (z : nadd) : (nadd_eq x z) = (nadd_eq x z).
Proof. exact (eq_refl (nadd_eq x z)). Qed.
Lemma lem1311680 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1311681 (x : nadd) (y : nadd) (z : nadd) : (term118 x y z) = (term119 x y z).
Proof. exact (MK_COMB (@lem1311680) (@lem1311678 x y z)). Qed.
Lemma lem1311682 (y : nadd) (x : nadd) (z : nadd) : (term120 y x z) = (term121 y x z).
Proof. exact (MK_COMB (@lem1311681 x y z) (@lem1311679 x z)). Qed.
Lemma lem1311683 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term120 y x z).
Proof. exact (@lem17265 (term14 x y z) (nadd_eq x z)). Qed.
Lemma lem1311684 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term121 y x z).
Proof. exact (TRANS (@lem1311683 y x z) (@lem1311682 y x z)). Qed.
Lemma lem1311685 (y : nadd) (x : nadd) : (term55 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1311684 y x z)). Qed.
Lemma lem1311686 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311687 (y : nadd) (x : nadd) : (term11 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1311686) (@lem1311685 y x)). Qed.
Lemma lem1311688 (x : nadd) : (term56 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1311687 y x)). Qed.
Lemma lem1311689 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311690 (x : nadd) : (term9 x) = (term125 x).
Proof. exact (MK_COMB (@lem1311689) (@lem1311688 x)). Qed.
Lemma lem1311691 : term57 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1311690 x)). Qed.
Lemma lem1311692 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311753 : term7 = term127.
Proof. exact (MK_COMB (@lem1311692) (@lem1311691)). Qed.
Lemma lem1311754 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1311753) (@lem1311645 h1)). Qed.
Lemma lem1311755 (x : nadd) : (term235 x) = (term235 x).
Proof. exact (eq_refl (term235 x)). Qed.
Lemma lem1311756 : term236 = term236.
Proof. exact (fun_ext (fun x : nadd => @lem1311755 x)). Qed.
Lemma lem1311757 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311766 : term237 = term237.
Proof. exact (MK_COMB (@lem1311757) (@lem1311756)). Qed.
Lemma lem1311767 (h1 : term237) : term237.
Proof. exact (EQ_MP (@lem1311766) (@lem1311646 h1)). Qed.
Lemma lem1311768 (y : nadd) (x : nadd) : (term231 y x) = (term231 y x).
Proof. exact (eq_refl (term231 y x)). Qed.
Lemma lem1311769 (x : nadd) : (term232 x) = (term232 x).
Proof. exact (fun_ext (fun y : nadd => @lem1311768 y x)). Qed.
Lemma lem1311770 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311771 (x : nadd) : (term233 x) = (term233 x).
Proof. exact (MK_COMB (@lem1311770) (@lem1311769 x)). Qed.
Lemma lem1311772 : term234 = term234.
Proof. exact (fun_ext (fun x : nadd => @lem1311771 x)). Qed.
Lemma lem1311773 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311786 : term208 = term208.
Proof. exact (MK_COMB (@lem1311773) (@lem1311772)). Qed.
Lemma lem1311787 (h1 : term208) : term208.
Proof. exact (EQ_MP (@lem1311786) (@lem1311647 h1)). Qed.
Lemma lem1311839 (y : nadd) (h1 : term201 y) : term201 y.
Proof. exact (h1). Qed.
Lemma lem1311864 (y : nadd) (x : nadd) (z : nadd) : (term121 y x z) = (term121 y x z).
Proof. exact (eq_refl (term121 y x z)). Qed.
Lemma lem1311865 (y : nadd) (x : nadd) : (term122 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1311864 y x z)). Qed.
Lemma lem1311866 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311867 (y : nadd) (x : nadd) : (term123 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1311866) (@lem1311865 y x)). Qed.
Lemma lem1311868 (x : nadd) : (term124 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1311867 y x)). Qed.
Lemma lem1311869 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311870 (x : nadd) : (term125 x) = (term125 x).
Proof. exact (MK_COMB (@lem1311869) (@lem1311868 x)). Qed.
Lemma lem1311871 : term126 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1311870 x)). Qed.
Lemma lem1311872 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311873 : term127 = term127.
Proof. exact (MK_COMB (@lem1311872) (@lem1311871)). Qed.
Lemma lem1311874 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1311873) (@lem1311754 h1)). Qed.
Lemma lem1311889 (x : nadd) : (term235 x) = (term235 x).
Proof. exact (eq_refl (term235 x)). Qed.
Lemma lem1311890 : term236 = term236.
Proof. exact (fun_ext (fun x : nadd => @lem1311889 x)). Qed.
Lemma lem1311891 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311892 : term237 = term237.
Proof. exact (MK_COMB (@lem1311891) (@lem1311890)). Qed.
Lemma lem1311893 (h1 : term237) : term237.
Proof. exact (EQ_MP (@lem1311892) (@lem1311767 h1)). Qed.
Lemma lem1311906 (y : nadd) (x : nadd) : (term231 y x) = (term231 y x).
Proof. exact (eq_refl (term231 y x)). Qed.
Lemma lem1311907 (x : nadd) : (term232 x) = (term232 x).
Proof. exact (fun_ext (fun y : nadd => @lem1311906 y x)). Qed.
Lemma lem1311908 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311909 (x : nadd) : (term233 x) = (term233 x).
Proof. exact (MK_COMB (@lem1311908) (@lem1311907 x)). Qed.
Lemma lem1311910 : term234 = term234.
Proof. exact (fun_ext (fun x : nadd => @lem1311909 x)). Qed.
Lemma lem1311911 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311912 : term208 = term208.
Proof. exact (MK_COMB (@lem1311911) (@lem1311910)). Qed.
Lemma lem1311913 (h1 : term208) : term208.
Proof. exact (EQ_MP (@lem1311912) (@lem1311787 h1)). Qed.
Lemma lem1311929 (y : nadd) (h1 : term201 y) : term201 y.
Proof. exact (h1). Qed.
Lemma lem1311943 (y : nadd) (x : nadd) (z : nadd) : (term121 y x z) = (term121 y x z).
Proof. exact (eq_refl (term121 y x z)). Qed.
Lemma lem1311944 (y : nadd) (x : nadd) : (term122 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1311943 y x z)). Qed.
Lemma lem1311945 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311946 (y : nadd) (x : nadd) : (term123 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1311945) (@lem1311944 y x)). Qed.
Lemma lem1311947 (x : nadd) : (term124 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1311946 y x)). Qed.
Lemma lem1311948 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311949 (x : nadd) : (term125 x) = (term125 x).
Proof. exact (MK_COMB (@lem1311948) (@lem1311947 x)). Qed.
Lemma lem1311950 : term126 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1311949 x)). Qed.
Lemma lem1311951 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311953 : term127 = term127.
Proof. exact (MK_COMB (@lem1311951) (@lem1311950)). Qed.
Lemma lem1311954 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1311953) (@lem1311874 h1)). Qed.
Lemma lem1311956 (x : nadd) : (term235 x) = (term235 x).
Proof. exact (eq_refl (term235 x)). Qed.
Lemma lem1311957 : term236 = term236.
Proof. exact (fun_ext (fun x : nadd => @lem1311956 x)). Qed.
Lemma lem1311958 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311960 : term237 = term237.
Proof. exact (MK_COMB (@lem1311958) (@lem1311957)). Qed.
Lemma lem1311961 (h1 : term237) : term237.
Proof. exact (EQ_MP (@lem1311960) (@lem1311893 h1)). Qed.
Lemma lem1311963 (y : nadd) (x : nadd) : (term231 y x) = (term231 y x).
Proof. exact (eq_refl (term231 y x)). Qed.
Lemma lem1311964 (x : nadd) : (term232 x) = (term232 x).
Proof. exact (fun_ext (fun y : nadd => @lem1311963 y x)). Qed.
Lemma lem1311965 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311966 (x : nadd) : (term233 x) = (term233 x).
Proof. exact (MK_COMB (@lem1311965) (@lem1311964 x)). Qed.
Lemma lem1311967 : term234 = term234.
Proof. exact (fun_ext (fun x : nadd => @lem1311966 x)). Qed.
Lemma lem1311968 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1311970 : term208 = term208.
Proof. exact (MK_COMB (@lem1311968) (@lem1311967)). Qed.
Lemma lem1311971 (h1 : term208) : term208.
Proof. exact (EQ_MP (@lem1311970) (@lem1311913 h1)). Qed.
Lemma lem1311972 (_23368 : nadd) (h1 : term7) : term128 _23368.
Proof. exact (@lem1311954 h1 _23368). Qed.
Lemma lem1311973 (_23368 : nadd) : (term128 _23368) = (term125 _23368).
Proof. exact (eq_refl (term128 _23368)). Qed.
Lemma lem1311974 (_23368 : nadd) (h1 : term7) : term125 _23368.
Proof. exact (EQ_MP (@lem1311973 _23368) (@lem1311972 _23368 h1)). Qed.
Lemma lem1311975 (_23368 : nadd) (_23369 : nadd) (h1 : term7) : term129 _23368 _23369.
Proof. exact (@lem1311974 _23368 h1 _23369). Qed.
Lemma lem1311976 (_23369 : nadd) (_23368 : nadd) : (term129 _23368 _23369) = (term123 _23369 _23368).
Proof. exact (eq_refl (term129 _23368 _23369)). Qed.
Lemma lem1311977 (_23369 : nadd) (_23368 : nadd) (h1 : term7) : term123 _23369 _23368.
Proof. exact (EQ_MP (@lem1311976 _23369 _23368) (@lem1311975 _23368 _23369 h1)). Qed.
Lemma lem1311978 (_23369 : nadd) (_23368 : nadd) (_23370 : nadd) (h1 : term7) : term130 _23369 _23368 _23370.
Proof. exact (@lem1311977 _23369 _23368 h1 _23370). Qed.
Lemma lem1311979 (_23369 : nadd) (_23368 : nadd) (_23370 : nadd) : (term130 _23369 _23368 _23370) = (term121 _23369 _23368 _23370).
Proof. exact (eq_refl (term130 _23369 _23368 _23370)). Qed.
Lemma lem1311980 (_23369 : nadd) (_23368 : nadd) (_23370 : nadd) (h1 : term7) : term121 _23369 _23368 _23370.
Proof. exact (EQ_MP (@lem1311979 _23369 _23368 _23370) (@lem1311978 _23369 _23368 _23370 h1)). Qed.
Lemma lem1311981 (_23371 : nadd) (h1 : term237) : term238 _23371.
Proof. exact (@lem1311961 h1 _23371). Qed.
Lemma lem1311982 (_23371 : nadd) : (term238 _23371) = (term235 _23371).
Proof. exact (eq_refl (term238 _23371)). Qed.
Lemma lem1311984 (_23372 : nadd) (h1 : term208) : term239 _23372.
Proof. exact (@lem1311971 h1 _23372). Qed.
Lemma lem1311985 (_23372 : nadd) : (term239 _23372) = (term233 _23372).
Proof. exact (eq_refl (term239 _23372)). Qed.
Lemma lem1311986 (_23372 : nadd) (h1 : term208) : term233 _23372.
Proof. exact (EQ_MP (@lem1311985 _23372) (@lem1311984 _23372 h1)). Qed.
Lemma lem1311987 (_23372 : nadd) (_23373 : nadd) (h1 : term208) : term240 _23372 _23373.
Proof. exact (@lem1311986 _23372 h1 _23373). Qed.
Lemma lem1311988 (_23373 : nadd) (_23372 : nadd) : (term240 _23372 _23373) = (term231 _23373 _23372).
Proof. exact (eq_refl (term240 _23372 _23373)). Qed.
Lemma lem1311997 (y : nadd) (h1 : term201 y) : term201 y.
Proof. exact (h1). Qed.
Lemma lem1312008 (_23369 : nadd) (_23368 : nadd) (_23370 : nadd) : (term121 _23369 _23368 _23370) = (term131 _23369 _23368 _23370).
Proof. exact (@lem1309156 (term132 _23368 _23369) (term132 _23369 _23370) (nadd_eq _23368 _23370)). Qed.
Lemma lem1312009 (_23369 : nadd) (_23368 : nadd) (_23370 : nadd) (h1 : term7) : term131 _23369 _23368 _23370.
Proof. exact (EQ_MP (@lem1312008 _23369 _23368 _23370) (@lem1311980 _23369 _23368 _23370 h1)). Qed.
Lemma lem1312015 (_23373 : nadd) (_23372 : nadd) (h1 : term208) : term231 _23373 _23372.
Proof. exact (EQ_MP (@lem1311988 _23373 _23372) (@lem1311987 _23372 _23373 h1)). Qed.
Lemma lem1312016 (y : nadd) (h1 : term208) : term241 y.
Proof. exact (@lem1312015 term242 (nadd_inv y) h1). Qed.
Lemma lem1312017 (y : nadd) (h1 : term208) : term243 y.
Proof. exact (fun h0 : term244 y => @lem1312016 y h1). Qed.
Lemma lem1312019 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1312020 (y : nadd) : (term243 y) = (term241 y).
Proof. exact (@lem1312019 (term241 y)). Qed.
Lemma lem1312021 (y : nadd) (h1 : term208) : term241 y.
Proof. exact (EQ_MP (@lem1312020 y) (@lem1312017 y h1)). Qed.
Lemma lem1312023 (_23371 : nadd) (h1 : term237) : term235 _23371.
Proof. exact (EQ_MP (@lem1311982 _23371) (@lem1311981 _23371 h1)). Qed.
Lemma lem1312024 (y : nadd) (h1 : term237) : term245 y.
Proof. exact (@lem1312023 (nadd_inv y) h1). Qed.
Lemma lem1312025 (y : nadd) (h1 : term237) : term246 y.
Proof. exact (fun h0 : term247 y => @lem1312024 y h1). Qed.
Lemma lem1312027 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1312028 (y : nadd) : (term246 y) = (term245 y).
Proof. exact (@lem1312027 (term245 y)). Qed.
Lemma lem1312029 (y : nadd) (h1 : term237) : term245 y.
Proof. exact (EQ_MP (@lem1312028 y) (@lem1312025 y h1)). Qed.
Lemma lem1312045 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1312046 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : (term144 _23369 _23368 _23370) = (term145 _23368 _23369 _23370).
Proof. exact (@lem1312045 (nadd_eq _23368 _23370) (term132 _23369 _23370)). Qed.
Lemma lem1312052 (_23368 : nadd) (_23369 : nadd) : (term146 _23368 _23369) = (term146 _23368 _23369).
Proof. exact (eq_refl (term146 _23368 _23369)). Qed.
Lemma lem1312053 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : (term131 _23369 _23368 _23370) = (term147 _23368 _23369 _23370).
Proof. exact (MK_COMB (@lem1312052 _23368 _23369) (@lem1312046 _23368 _23369 _23370)). Qed.
Lemma lem1312057 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1312058 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : (term147 _23368 _23369 _23370) = (term148 _23368 _23369 _23370).
Proof. exact (@lem1312057 (nadd_eq _23368 _23370) (term132 _23368 _23369) (term132 _23369 _23370)). Qed.
Lemma lem1312074 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : (term131 _23369 _23368 _23370) = (term148 _23368 _23369 _23370).
Proof. exact (TRANS (@lem1312053 _23368 _23369 _23370) (@lem1312058 _23368 _23369 _23370)). Qed.
Lemma lem1312075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1312076 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : (term149 _23369 _23368 _23370) = (term150 _23368 _23369 _23370).
Proof. exact (MK_COMB (@lem1312075) (@lem1312074 _23368 _23369 _23370)). Qed.
Lemma lem1312092 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : (term148 _23368 _23369 _23370) = (term148 _23368 _23369 _23370).
Proof. exact (eq_refl (term148 _23368 _23369 _23370)). Qed.
Lemma lem1312093 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : ((term131 _23369 _23368 _23370) = (term148 _23368 _23369 _23370)) = ((term148 _23368 _23369 _23370) = (term148 _23368 _23369 _23370)).
Proof. exact (MK_COMB (@lem1312076 _23368 _23369 _23370) (@lem1312092 _23368 _23369 _23370)). Qed.
Lemma lem1312095 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1312096 (x : Prop) : (x = x) = True.
Proof. exact (@lem1312095 Prop x). Qed.
Lemma lem1312097 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : ((term148 _23368 _23369 _23370) = (term148 _23368 _23369 _23370)) = True.
Proof. exact (@lem1312096 (term148 _23368 _23369 _23370)). Qed.
Lemma lem1312098 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : ((term131 _23369 _23368 _23370) = (term148 _23368 _23369 _23370)) = True.
Proof. exact (TRANS (@lem1312093 _23368 _23369 _23370) (@lem1312097 _23368 _23369 _23370)). Qed.
Lemma lem1312099 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : True = ((term131 _23369 _23368 _23370) = (term148 _23368 _23369 _23370)).
Proof. exact (SYM (@lem1312098 _23368 _23369 _23370)). Qed.
Lemma lem1312100 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : (term131 _23369 _23368 _23370) = (term148 _23368 _23369 _23370).
Proof. exact (EQ_MP (@lem1312099 _23368 _23369 _23370) (@lem0)). Qed.
Lemma lem1312101 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) (h1 : term7) : term148 _23368 _23369 _23370.
Proof. exact (EQ_MP (@lem1312100 _23368 _23369 _23370) (@lem1312009 _23369 _23368 _23370 h1)). Qed.
Lemma lem1312103 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1312104 (_23369 : nadd) (_23368 : nadd) (_23370 : nadd) : (term148 _23368 _23369 _23370) = (term151 _23369 _23368 _23370).
Proof. exact (@lem1312103 (term117 _23368 _23369 _23370) (nadd_eq _23368 _23370)). Qed.
Lemma lem1312106 (a : Prop) (b : Prop) : (term152 a b) = (term153 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1312107 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : (term154 _23368 _23369 _23370) = (term155 _23368 _23369 _23370).
Proof. exact (@lem1312106 (term132 _23368 _23369) (term132 _23369 _23370)). Qed.
Lemma lem1312109 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1312110 (_23368 : nadd) (_23369 : nadd) : (term140 _23368 _23369) = (nadd_eq _23368 _23369).
Proof. exact (@lem1312109 (nadd_eq _23368 _23369)). Qed.
Lemma lem1312111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1312112 (_23368 : nadd) (_23369 : nadd) : (term156 _23368 _23369) = (term157 _23368 _23369).
Proof. exact (MK_COMB (@lem1312111) (@lem1312110 _23368 _23369)). Qed.
Lemma lem1312114 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1312115 (_23369 : nadd) (_23370 : nadd) : (term140 _23369 _23370) = (nadd_eq _23369 _23370).
Proof. exact (@lem1312114 (nadd_eq _23369 _23370)). Qed.
Lemma lem1312116 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : (term155 _23368 _23369 _23370) = (term14 _23368 _23369 _23370).
Proof. exact (MK_COMB (@lem1312112 _23368 _23369) (@lem1312115 _23369 _23370)). Qed.
Lemma lem1312117 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : (term154 _23368 _23369 _23370) = (term14 _23368 _23369 _23370).
Proof. exact (TRANS (@lem1312107 _23368 _23369 _23370) (@lem1312116 _23368 _23369 _23370)). Qed.
Lemma lem1312118 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1312119 (_23368 : nadd) (_23369 : nadd) (_23370 : nadd) : (term158 _23368 _23369 _23370) = (term159 _23368 _23369 _23370).
Proof. exact (MK_COMB (@lem1312118) (@lem1312117 _23368 _23369 _23370)). Qed.
Lemma lem1312120 (_23368 : nadd) (_23370 : nadd) : (nadd_eq _23368 _23370) = (nadd_eq _23368 _23370).
Proof. exact (eq_refl (nadd_eq _23368 _23370)). Qed.
Lemma lem1312121 (_23369 : nadd) (_23368 : nadd) (_23370 : nadd) : (term151 _23369 _23368 _23370) = (term13 _23369 _23368 _23370).
Proof. exact (MK_COMB (@lem1312119 _23368 _23369 _23370) (@lem1312120 _23368 _23370)). Qed.
Lemma lem1312122 (_23369 : nadd) (_23368 : nadd) (_23370 : nadd) : (term148 _23368 _23369 _23370) = (term13 _23369 _23368 _23370).
Proof. exact (TRANS (@lem1312104 _23369 _23368 _23370) (@lem1312121 _23369 _23368 _23370)). Qed.
Lemma lem1312124 (y : nadd) (h1 : term208) (h2 : term237) : term248 y.
Proof. exact (conj (@lem1312021 y h1) (@lem1312029 y h2)). Qed.
Lemma lem1312126 (_23369 : nadd) (_23368 : nadd) (_23370 : nadd) (h1 : term7) : term13 _23369 _23368 _23370.
Proof. exact (EQ_MP (@lem1312122 _23369 _23368 _23370) (@lem1312101 _23368 _23369 _23370 h1)). Qed.
Lemma lem1312127 (y : nadd) (h1 : term7) : term249 y.
Proof. exact (@lem1312126 (term250 y) (term251 y) (nadd_inv y) h1). Qed.
Lemma lem1312130 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) : term199 y.
Proof. exact (@lem1312127 y h1 (@lem1312124 y h2 h3)). Qed.
Lemma lem1312131 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) : term252 y.
Proof. exact (fun h0 : term201 y => @lem1312130 y h1 h2 h3). Qed.
Lemma lem1312133 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1312134 (y : nadd) : (term252 y) = (term199 y).
Proof. exact (@lem1312133 (term199 y)). Qed.
Lemma lem1312135 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) : term199 y.
Proof. exact (EQ_MP (@lem1312134 y) (@lem1312131 y h1 h2 h3)). Qed.
Lemma lem1312138 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1312140 (y : nadd) : (term201 y) = (term253 y).
Proof. exact (@lem1312138 (term199 y)). Qed.
Lemma lem1312143 (y : nadd) (h1 : term201 y) : term253 y.
Proof. exact (EQ_MP (@lem1312140 y) (@lem1311997 y h1)). Qed.
Lemma lem1312146 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : False.
Proof. exact (@lem1312143 y h4 (@lem1312135 y h1 h2 h3)). Qed.
Lemma lem1312147 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : term164.
Proof. exact (fun h0 : ~ False => @lem1312146 y h1 h2 h3 h4). Qed.
Lemma lem1312149 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1312150 : term164 = False.
Proof. exact (@lem1312149 False). Qed.
Lemma lem1312151 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : False.
Proof. exact (EQ_MP (@lem1312150) (@lem1312147 y h1 h2 h3 h4)). Qed.
Lemma lem1312152 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : (term201 y) = False.
Proof. exact (prop_ext (fun h5 : term201 y => @lem1312151 y h1 h2 h3 h4) (fun h5 : False => @lem1311997 y h4)). Qed.
Lemma lem1312153 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : False.
Proof. exact (EQ_MP (@lem1312152 y h1 h2 h3 h4) (@lem1311997 y h4)). Qed.
Lemma lem1312154 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : (term201 y) = False.
Proof. exact (prop_ext (fun h5 : term201 y => @lem1312153 y h1 h2 h3 h4) (fun h5 : False => @lem1311929 y h4)). Qed.
Lemma lem1312155 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : False.
Proof. exact (EQ_MP (@lem1312154 y h1 h2 h3 h4) (@lem1311929 y h4)). Qed.
Lemma lem1312156 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : term208 = False.
Proof. exact (prop_ext (fun h5 : term208 => @lem1312155 y h1 h2 h3 h4) (fun h5 : False => @lem1311971 h2)). Qed.
Lemma lem1312157 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : False.
Proof. exact (EQ_MP (@lem1312156 y h1 h2 h3 h4) (@lem1311971 h2)). Qed.
Lemma lem1312158 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : term237 = False.
Proof. exact (prop_ext (fun h5 : term237 => @lem1312157 y h1 h2 h3 h4) (fun h5 : False => @lem1311961 h3)). Qed.
Lemma lem1312159 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : False.
Proof. exact (EQ_MP (@lem1312158 y h1 h2 h3 h4) (@lem1311961 h3)). Qed.
Lemma lem1312160 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : (term201 y) = False.
Proof. exact (prop_ext (fun h5 : term201 y => @lem1312159 y h1 h2 h3 h4) (fun h5 : False => @lem1311929 y h4)). Qed.
Lemma lem1312161 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : False.
Proof. exact (EQ_MP (@lem1312160 y h1 h2 h3 h4) (@lem1311929 y h4)). Qed.
Lemma lem1312162 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : term208 = False.
Proof. exact (prop_ext (fun h5 : term208 => @lem1312161 y h1 h2 h3 h4) (fun h5 : False => @lem1311913 h2)). Qed.
Lemma lem1312163 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : False.
Proof. exact (EQ_MP (@lem1312162 y h1 h2 h3 h4) (@lem1311913 h2)). Qed.
Lemma lem1312164 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : term237 = False.
Proof. exact (prop_ext (fun h5 : term237 => @lem1312163 y h1 h2 h3 h4) (fun h5 : False => @lem1311893 h3)). Qed.
Lemma lem1312165 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : False.
Proof. exact (EQ_MP (@lem1312164 y h1 h2 h3 h4) (@lem1311893 h3)). Qed.
Lemma lem1312166 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : (term201 y) = False.
Proof. exact (prop_ext (fun h5 : term201 y => @lem1312165 y h1 h2 h3 h4) (fun h5 : False => @lem1311839 y h4)). Qed.
Lemma lem1312167 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : False.
Proof. exact (EQ_MP (@lem1312166 y h1 h2 h3 h4) (@lem1311839 y h4)). Qed.
Lemma lem1312168 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : term208 = False.
Proof. exact (prop_ext (fun h5 : term208 => @lem1312167 y h1 h2 h3 h4) (fun h5 : False => @lem1311787 h2)). Qed.
Lemma lem1312169 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : False.
Proof. exact (EQ_MP (@lem1312168 y h1 h2 h3 h4) (@lem1311787 h2)). Qed.
Lemma lem1312170 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : term237 = False.
Proof. exact (prop_ext (fun h5 : term237 => @lem1312169 y h1 h2 h3 h4) (fun h5 : False => @lem1311767 h3)). Qed.
Lemma lem1312171 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : False.
Proof. exact (EQ_MP (@lem1312170 y h1 h2 h3 h4) (@lem1311767 h3)). Qed.
Lemma lem1312172 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : (term201 y) = False.
Proof. exact (prop_ext (fun h5 : term201 y => @lem1312171 y h1 h2 h3 h4) (fun h5 : False => @lem1311671 y h4)). Qed.
Lemma lem1312173 (y : nadd) (h1 : term7) (h2 : term208) (h3 : term237) (h4 : term201 y) : False.
Proof. exact (EQ_MP (@lem1312172 y h1 h2 h3 h4) (@lem1311671 y h4)). Qed.
Lemma lem1312174 (y : nadd) (h1 : term7) (h2 : term237) (h3 : term201 y) : term206.
Proof. exact (fun h0 : term208 => @lem1312173 y h1 h0 h2 h3). Qed.
Lemma lem1312175 : term206 = term207.
Proof. exact (@lem69 term208). Qed.
Lemma lem1312176 (y : nadd) (h1 : term7) (h2 : term237) (h3 : term201 y) : term207.
Proof. exact (EQ_MP (@lem1312175) (@lem1312174 y h1 h2 h3)). Qed.
Lemma lem1312177 (y : nadd) (h1 : term7) (h2 : term201 y) : term211.
Proof. exact (fun h0 : term237 => @lem1312176 y h1 h0 h2). Qed.
Lemma lem1312178 (y : nadd) (h1 : term201 y) : term214.
Proof. exact (fun h0 : term7 => @lem1312177 y h0 h1). Qed.
Lemma lem1312179 (y : nadd) : term217 y.
Proof. exact (fun h0 : term201 y => @lem1312178 y h0). Qed.
Lemma lem1312180 (y : nadd) : term219 y.
Proof. exact (fun h0 : term27 y => @lem1312179 y). Qed.
Lemma lem1312181 (x : nadd) (y : nadd) : term221 x y.
Proof. exact (fun h0 : term27 x => @lem1312180 y). Qed.
Lemma lem1312182 (x : nadd) (y : nadd) : term222 x y.
Proof. exact (fun h0 : nadd_eq x y => @lem1312181 x y). Qed.
Lemma lem1312187 (y : nadd) : term226 y.
Proof. exact (fun x : nadd => @lem1312182 x y). Qed.
Lemma lem1312192 : term230.
Proof. exact (fun y : nadd => @lem1312187 y). Qed.
Lemma lem1312193 : term229.
Proof. exact (EQ_MP (@lem1311640) (@lem1312192)). Qed.
Lemma lem1312194 (y : nadd) : term254 y.
Proof. exact (@lem1312193 y). Qed.
Lemma lem1312195 (y : nadd) : (term254 y) = (term225 y).
Proof. exact (eq_refl (term254 y)). Qed.
Lemma lem1312196 (y : nadd) : term225 y.
Proof. exact (EQ_MP (@lem1312195 y) (@lem1312194 y)). Qed.
Lemma lem1312197 (y : nadd) (x : nadd) : term255 y x.
Proof. exact (@lem1312196 y x). Qed.
Lemma lem1312198 (x : nadd) (y : nadd) : (term255 y x) = (term202 x y).
Proof. exact (eq_refl (term255 y x)). Qed.
Lemma lem1312199 (x : nadd) (y : nadd) : term202 x y.
Proof. exact (EQ_MP (@lem1312198 x y) (@lem1312197 y x)). Qed.
Lemma lem1312201 (x : nadd) (y : nadd) : term202 x y.
Proof. exact (@lem1311414 x y (@lem1312199 x y)). Qed.
Lemma lem1312202 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term220 x y.
Proof. exact (@lem1312201 x y (@lem1309210 x y h1)). Qed.
Lemma lem1312203 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) : term218 y.
Proof. exact (@lem1312202 x y h2 (@lem1309209 x h1)). Qed.
Lemma lem1312204 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term216 y.
Proof. exact (@lem1312203 x y h1 h3 (@lem1310360 y h2)). Qed.
Lemma lem1312205 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term201 y) (h4 : nadd_eq x y) : term213.
Proof. exact (@lem1312204 x y h1 h2 h4 (@lem1311399 y h3)). Qed.
Lemma lem1312206 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term201 y) (h4 : nadd_eq x y) : term210.
Proof. exact (@lem1312205 x y h1 h2 h3 h4 (@lem1268295)). Qed.
Lemma lem1312207 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term201 y) (h4 : nadd_eq x y) : term206.
Proof. exact (@lem1312206 x y h1 h2 h3 h4 (@lem1278627)). Qed.
Lemma lem1312208 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term201 y) (h4 : nadd_eq x y) : False.
Proof. exact (@lem1312207 x y h1 h2 h3 h4 (@lem1278399)). Qed.
Lemma lem1312209 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term201 y) (h4 : nadd_eq x y) : (term201 y) = False.
Proof. exact (prop_ext (fun h5 : term201 y => @lem1312208 x y h1 h2 h3 h4) (fun h5 : False => @lem1311399 y h3)). Qed.
Lemma lem1312210 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term201 y) (h4 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1312209 x y h1 h2 h3 h4) (@lem1311399 y h3)). Qed.
Lemma lem1312211 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term200 y.
Proof. exact (fun h0 : term201 y => @lem1312210 x y h1 h2 h0 h3). Qed.
Lemma lem1312212 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term199 y.
Proof. exact (EQ_MP (@lem1311398 y) (@lem1312211 x y h1 h2 h3)). Qed.
Lemma lem1312214 (x : nadd) (z : nadd) : term18 x z.
Proof. exact (EQ_MP (@lem1309145 x z) (@lem1309144 x z)). Qed.
Lemma lem1312215 (x : nadd) (y : nadd) : term256 x y.
Proof. exact (@lem1312214 (nadd_inv x) (term251 y)). Qed.
Lemma lem1312217 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1312218 (x : nadd) (y : nadd) : (term257 x y) = (term258 x y).
Proof. exact (@lem1312217 (term257 x y)). Qed.
Lemma lem1312219 (x : nadd) (y : nadd) : (term258 x y) = (term257 x y).
Proof. exact (SYM (@lem1312218 x y)). Qed.
Lemma lem1312220 (x : nadd) (y : nadd) (h1 : term259 x y) : term259 x y.
Proof. exact (h1). Qed.
Lemma lem1312223 (x : nadd) (y : nadd) (h1 : term260 x y) : term260 x y.
Proof. exact (h1). Qed.
Lemma lem1312224 (x : nadd) (y : nadd) : term261 x y.
Proof. exact (fun h0 : term260 x y => @lem1312223 x y h0). Qed.
Lemma lem1312225 (x : nadd) (y : nadd) (h1 : term261 x y) : term261 x y.
Proof. exact (h1). Qed.
Lemma lem1312226 (x : nadd) (y : nadd) (h1 : term260 x y) : term260 x y.
Proof. exact (h1). Qed.
Lemma lem1312227 (x : nadd) (y : nadd) (h1 : term261 x y) (h2 : term260 x y) : term260 x y.
Proof. exact (@lem1312225 x y h1 (@lem1312226 x y h2)). Qed.
Lemma lem1312228 (x : nadd) (y : nadd) (h1 : term260 x y) : term262 x y.
Proof. exact (fun h0 : term261 x y => @lem1312227 x y h0 h1). Qed.
Lemma lem1312229 (x : nadd) (y : nadd) (h1 : term261 x y) : term261 x y.
Proof. exact (h1). Qed.
Lemma lem1312230 (x : nadd) (y : nadd) (h1 : term261 x y) (h2 : term260 x y) : term260 x y.
Proof. exact (@lem1312228 x y h2 (@lem1312229 x y h1)). Qed.
Lemma lem1312231 (x : nadd) (y : nadd) (h1 : term261 x y) : term261 x y.
Proof. exact (fun h0 : term260 x y => @lem1312230 x y h1 h0). Qed.
Lemma lem1312232 (x : nadd) (y : nadd) : term263 x y.
Proof. exact (fun h0 : term261 x y => @lem1312231 x y h0). Qed.
Lemma lem1312235 (x : nadd) (y : nadd) : term261 x y.
Proof. exact (@lem1312232 x y (@lem1312224 x y)). Qed.
Lemma lem1312281 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1312282 : term264 = term265.
Proof. exact (@lem1312281 term266). Qed.
Lemma lem1312289 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem1312290 : term268 = term269.
Proof. exact (MK_COMB (@lem1312289) (@lem1312282)). Qed.
Lemma lem1312293 : term270 = term270.
Proof. exact (eq_refl term270). Qed.
Lemma lem1312294 : term271 = term272.
Proof. exact (MK_COMB (@lem1312293) (@lem1312290)). Qed.
Lemma lem1312297 (x : nadd) (y : nadd) : (term273 x y) = (term273 x y).
Proof. exact (eq_refl (term273 x y)). Qed.
Lemma lem1312298 (x : nadd) (y : nadd) : (term274 x y) = (term275 x y).
Proof. exact (MK_COMB (@lem1312297 x y) (@lem1312294)). Qed.
Lemma lem1312301 (y : nadd) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem1312302 (x : nadd) (y : nadd) : (term276 x y) = (term277 x y).
Proof. exact (MK_COMB (@lem1312301 y) (@lem1312298 x y)). Qed.
Lemma lem1312305 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1312306 (x : nadd) (y : nadd) : (term278 x y) = (term279 x y).
Proof. exact (MK_COMB (@lem1312305 x) (@lem1312302 x y)). Qed.
Lemma lem1312309 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1312310 (x : nadd) (y : nadd) : (term260 x y) = (term280 x y).
Proof. exact (MK_COMB (@lem1312309 x y) (@lem1312306 x y)). Qed.
Lemma lem1312313 (y : nadd) : (term281 y) = (term282 y).
Proof. exact (fun_ext (fun x : nadd => @lem1312310 x y)). Qed.
Lemma lem1312314 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312315 (y : nadd) : (term283 y) = (term284 y).
Proof. exact (MK_COMB (@lem1312314) (@lem1312313 y)). Qed.
Lemma lem1312320 : term285 = term286.
Proof. exact (fun_ext (fun y : nadd => @lem1312315 y)). Qed.
Lemma lem1312321 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312330 : term287 = term288.
Proof. exact (MK_COMB (@lem1312321) (@lem1312320)). Qed.
Lemma lem1312337 (x : nadd) : (term289 x) = (term289 x).
Proof. exact (eq_refl (term289 x)). Qed.
Lemma lem1312338 : term290 = term290.
Proof. exact (fun_ext (fun x : nadd => @lem1312337 x)). Qed.
Lemma lem1312339 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312340 : term266 = term266.
Proof. exact (MK_COMB (@lem1312339) (@lem1312338)). Qed.
Lemma lem1312341 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1312342 : term265 = term265.
Proof. exact (MK_COMB (@lem1312341) (@lem1312340)). Qed.
Lemma lem1312351 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term291 x y x' y') = (term291 x y x' y').
Proof. exact (eq_refl (term291 x y x' y')). Qed.
Lemma lem1312352 (x : nadd) (y : nadd) (x' : nadd) : (term292 x y x') = (term292 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1312351 x y x' y')). Qed.
Lemma lem1312353 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312354 (x : nadd) (y : nadd) (x' : nadd) : (term293 x y x') = (term293 x y x').
Proof. exact (MK_COMB (@lem1312353) (@lem1312352 x y x')). Qed.
Lemma lem1312355 (x : nadd) (x' : nadd) : (term294 x x') = (term294 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1312354 x y x')). Qed.
Lemma lem1312356 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312357 (x : nadd) (x' : nadd) : (term295 x x') = (term295 x x').
Proof. exact (MK_COMB (@lem1312356) (@lem1312355 x x')). Qed.
Lemma lem1312358 (x : nadd) : (term296 x) = (term296 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1312357 x x')). Qed.
Lemma lem1312359 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312360 (x : nadd) : (term297 x) = (term297 x).
Proof. exact (MK_COMB (@lem1312359) (@lem1312358 x)). Qed.
Lemma lem1312361 : term298 = term298.
Proof. exact (fun_ext (fun x : nadd => @lem1312360 x)). Qed.
Lemma lem1312362 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312363 : term299 = term299.
Proof. exact (MK_COMB (@lem1312362) (@lem1312361)). Qed.
Lemma lem1312364 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1312365 : term267 = term267.
Proof. exact (MK_COMB (@lem1312364) (@lem1312363)). Qed.
Lemma lem1312366 : term269 = term269.
Proof. exact (MK_COMB (@lem1312365) (@lem1312342)). Qed.
Lemma lem1312367 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1312368 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1312367 x)). Qed.
Lemma lem1312369 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312370 : term301 = term301.
Proof. exact (MK_COMB (@lem1312369) (@lem1312368)). Qed.
Lemma lem1312371 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1312372 : term270 = term270.
Proof. exact (MK_COMB (@lem1312371) (@lem1312370)). Qed.
Lemma lem1312373 : term272 = term272.
Proof. exact (MK_COMB (@lem1312372) (@lem1312366)). Qed.
Lemma lem1312378 (x : nadd) (y : nadd) : (term273 x y) = (term273 x y).
Proof. exact (eq_refl (term273 x y)). Qed.
Lemma lem1312379 (x : nadd) (y : nadd) : (term275 x y) = (term275 x y).
Proof. exact (MK_COMB (@lem1312378 x y) (@lem1312373)). Qed.
Lemma lem1312384 (y : nadd) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem1312385 (x : nadd) (y : nadd) : (term277 x y) = (term277 x y).
Proof. exact (MK_COMB (@lem1312384 y) (@lem1312379 x y)). Qed.
Lemma lem1312390 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1312391 (x : nadd) (y : nadd) : (term279 x y) = (term279 x y).
Proof. exact (MK_COMB (@lem1312390 x) (@lem1312385 x y)). Qed.
Lemma lem1312394 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1312395 (x : nadd) (y : nadd) : (term280 x y) = (term280 x y).
Proof. exact (MK_COMB (@lem1312394 x y) (@lem1312391 x y)). Qed.
Lemma lem1312396 (y : nadd) : (term282 y) = (term282 y).
Proof. exact (fun_ext (fun x : nadd => @lem1312395 x y)). Qed.
Lemma lem1312397 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312398 (y : nadd) : (term284 y) = (term284 y).
Proof. exact (MK_COMB (@lem1312397) (@lem1312396 y)). Qed.
Lemma lem1312399 : term286 = term286.
Proof. exact (fun_ext (fun y : nadd => @lem1312398 y)). Qed.
Lemma lem1312400 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312401 : term288 = term288.
Proof. exact (MK_COMB (@lem1312400) (@lem1312399)). Qed.
Lemma lem1312470 : term287 = term288.
Proof. exact (TRANS (@lem1312330) (@lem1312401)). Qed.
Lemma lem1312471 : term288 = term287.
Proof. exact (SYM (@lem1312470)). Qed.
Lemma lem1312476 (h1 : term301) : term301.
Proof. exact (h1). Qed.
Lemma lem1312477 (h1 : term299) : term299.
Proof. exact (h1). Qed.
Lemma lem1312478 (h1 : term266) : term266.
Proof. exact (h1). Qed.
Lemma lem1312490 (x : nadd) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1312502 (x : nadd) (y : nadd) (h1 : term259 x y) : term259 x y.
Proof. exact (h1). Qed.
Lemma lem1312503 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1312504 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1312503 x)). Qed.
Lemma lem1312505 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312514 : term301 = term301.
Proof. exact (MK_COMB (@lem1312505) (@lem1312504)). Qed.
Lemma lem1312515 (h1 : term301) : term301.
Proof. exact (EQ_MP (@lem1312514) (@lem1312476 h1)). Qed.
Lemma lem1312522 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term302 x x' y y') = (term303 x x' y y').
Proof. exact (@lem17045 (nadd_eq x x') (nadd_eq y y')). Qed.
Lemma lem1312523 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term304 x y x' y') = (term304 x y x' y').
Proof. exact (eq_refl (term304 x y x' y')). Qed.
Lemma lem1312524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1312525 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term305 x x' y y') = (term306 x x' y y').
Proof. exact (MK_COMB (@lem1312524) (@lem1312522 x x' y y')). Qed.
Lemma lem1312526 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term307 x y x' y') = (term308 x y x' y').
Proof. exact (MK_COMB (@lem1312525 x x' y y') (@lem1312523 x y x' y')). Qed.
Lemma lem1312527 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term291 x y x' y') = (term307 x y x' y').
Proof. exact (@lem17265 (term309 x x' y y') (term304 x y x' y')). Qed.
Lemma lem1312528 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term291 x y x' y') = (term308 x y x' y').
Proof. exact (TRANS (@lem1312527 x y x' y') (@lem1312526 x y x' y')). Qed.
Lemma lem1312529 (x : nadd) (y : nadd) (x' : nadd) : (term292 x y x') = (term310 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1312528 x y x' y')). Qed.
Lemma lem1312530 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312531 (x : nadd) (y : nadd) (x' : nadd) : (term293 x y x') = (term311 x y x').
Proof. exact (MK_COMB (@lem1312530) (@lem1312529 x y x')). Qed.
Lemma lem1312532 (x : nadd) (x' : nadd) : (term294 x x') = (term312 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1312531 x y x')). Qed.
Lemma lem1312533 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312534 (x : nadd) (x' : nadd) : (term295 x x') = (term313 x x').
Proof. exact (MK_COMB (@lem1312533) (@lem1312532 x x')). Qed.
Lemma lem1312535 (x : nadd) : (term296 x) = (term314 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1312534 x x')). Qed.
Lemma lem1312536 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312537 (x : nadd) : (term297 x) = (term315 x).
Proof. exact (MK_COMB (@lem1312536) (@lem1312535 x)). Qed.
Lemma lem1312538 : term298 = term316.
Proof. exact (fun_ext (fun x : nadd => @lem1312537 x)). Qed.
Lemma lem1312539 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312604 : term299 = term317.
Proof. exact (MK_COMB (@lem1312539) (@lem1312538)). Qed.
Lemma lem1312605 (h1 : term299) : term317.
Proof. exact (EQ_MP (@lem1312604) (@lem1312477 h1)). Qed.
Lemma lem1312608 (x : nadd) : (term318 x) = (term25 x).
Proof. exact (@lem16933 (term25 x)). Qed.
Lemma lem1312609 (x : nadd) : (term319 x) = (term319 x).
Proof. exact (eq_refl (term319 x)). Qed.
Lemma lem1312610 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1312611 (x : nadd) : (term320 x) = (term321 x).
Proof. exact (MK_COMB (@lem1312610) (@lem1312608 x)). Qed.
Lemma lem1312612 (x : nadd) : (term322 x) = (term323 x).
Proof. exact (MK_COMB (@lem1312611 x) (@lem1312609 x)). Qed.
Lemma lem1312613 (x : nadd) : (term289 x) = (term322 x).
Proof. exact (@lem17265 (term27 x) (term319 x)). Qed.
Lemma lem1312614 (x : nadd) : (term289 x) = (term323 x).
Proof. exact (TRANS (@lem1312613 x) (@lem1312612 x)). Qed.
Lemma lem1312615 : term290 = term324.
Proof. exact (fun_ext (fun x : nadd => @lem1312614 x)). Qed.
Lemma lem1312616 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312669 : term266 = term325.
Proof. exact (MK_COMB (@lem1312616) (@lem1312615)). Qed.
Lemma lem1312670 (h1 : term266) : term325.
Proof. exact (EQ_MP (@lem1312669) (@lem1312478 h1)). Qed.
Lemma lem1312688 (x : nadd) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1312732 (x : nadd) (y : nadd) (h1 : term259 x y) : term259 x y.
Proof. exact (h1). Qed.
Lemma lem1312737 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1312738 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1312737 x)). Qed.
Lemma lem1312739 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312740 : term301 = term301.
Proof. exact (MK_COMB (@lem1312739) (@lem1312738)). Qed.
Lemma lem1312741 (h1 : term301) : term301.
Proof. exact (EQ_MP (@lem1312740) (@lem1312515 h1)). Qed.
Lemma lem1312774 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term308 x y x' y') = (term308 x y x' y').
Proof. exact (eq_refl (term308 x y x' y')). Qed.
Lemma lem1312775 (x : nadd) (y : nadd) (x' : nadd) : (term310 x y x') = (term310 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1312774 x y x' y')). Qed.
Lemma lem1312776 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312777 (x : nadd) (y : nadd) (x' : nadd) : (term311 x y x') = (term311 x y x').
Proof. exact (MK_COMB (@lem1312776) (@lem1312775 x y x')). Qed.
Lemma lem1312778 (x : nadd) (x' : nadd) : (term312 x x') = (term312 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1312777 x y x')). Qed.
Lemma lem1312779 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312780 (x : nadd) (x' : nadd) : (term313 x x') = (term313 x x').
Proof. exact (MK_COMB (@lem1312779) (@lem1312778 x x')). Qed.
Lemma lem1312781 (x : nadd) : (term314 x) = (term314 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1312780 x x')). Qed.
Lemma lem1312782 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312783 (x : nadd) : (term315 x) = (term315 x).
Proof. exact (MK_COMB (@lem1312782) (@lem1312781 x)). Qed.
Lemma lem1312784 : term316 = term316.
Proof. exact (fun_ext (fun x : nadd => @lem1312783 x)). Qed.
Lemma lem1312785 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312786 : term317 = term317.
Proof. exact (MK_COMB (@lem1312785) (@lem1312784)). Qed.
Lemma lem1312787 (h1 : term299) : term317.
Proof. exact (EQ_MP (@lem1312786) (@lem1312605 h1)). Qed.
Lemma lem1312816 (x : nadd) : (term323 x) = (term323 x).
Proof. exact (eq_refl (term323 x)). Qed.
Lemma lem1312817 : term324 = term324.
Proof. exact (fun_ext (fun x : nadd => @lem1312816 x)). Qed.
Lemma lem1312818 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312819 : term325 = term325.
Proof. exact (MK_COMB (@lem1312818) (@lem1312817)). Qed.
Lemma lem1312820 (h1 : term266) : term325.
Proof. exact (EQ_MP (@lem1312819) (@lem1312670 h1)). Qed.
Lemma lem1312828 (x : nadd) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1312836 (x : nadd) (y : nadd) (h1 : term259 x y) : term259 x y.
Proof. exact (h1). Qed.
Lemma lem1312838 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1312839 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1312838 x)). Qed.
Lemma lem1312840 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312842 : term301 = term301.
Proof. exact (MK_COMB (@lem1312840) (@lem1312839)). Qed.
Lemma lem1312843 (h1 : term301) : term301.
Proof. exact (EQ_MP (@lem1312842) (@lem1312741 h1)). Qed.
Lemma lem1312857 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term308 x y x' y') = (term308 x y x' y').
Proof. exact (eq_refl (term308 x y x' y')). Qed.
Lemma lem1312858 (x : nadd) (y : nadd) (x' : nadd) : (term310 x y x') = (term310 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1312857 x y x' y')). Qed.
Lemma lem1312859 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312860 (x : nadd) (y : nadd) (x' : nadd) : (term311 x y x') = (term311 x y x').
Proof. exact (MK_COMB (@lem1312859) (@lem1312858 x y x')). Qed.
Lemma lem1312861 (x : nadd) (x' : nadd) : (term312 x x') = (term312 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1312860 x y x')). Qed.
Lemma lem1312862 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312863 (x : nadd) (x' : nadd) : (term313 x x') = (term313 x x').
Proof. exact (MK_COMB (@lem1312862) (@lem1312861 x x')). Qed.
Lemma lem1312864 (x : nadd) : (term314 x) = (term314 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1312863 x x')). Qed.
Lemma lem1312865 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312866 (x : nadd) : (term315 x) = (term315 x).
Proof. exact (MK_COMB (@lem1312865) (@lem1312864 x)). Qed.
Lemma lem1312867 : term316 = term316.
Proof. exact (fun_ext (fun x : nadd => @lem1312866 x)). Qed.
Lemma lem1312868 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312870 : term317 = term317.
Proof. exact (MK_COMB (@lem1312868) (@lem1312867)). Qed.
Lemma lem1312871 (h1 : term299) : term317.
Proof. exact (EQ_MP (@lem1312870) (@lem1312787 h1)). Qed.
Lemma lem1312879 (x : nadd) : (term323 x) = (term323 x).
Proof. exact (eq_refl (term323 x)). Qed.
Lemma lem1312880 : term324 = term324.
Proof. exact (fun_ext (fun x : nadd => @lem1312879 x)). Qed.
Lemma lem1312881 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1312883 : term325 = term325.
Proof. exact (MK_COMB (@lem1312881) (@lem1312880)). Qed.
Lemma lem1312884 (h1 : term266) : term325.
Proof. exact (EQ_MP (@lem1312883) (@lem1312820 h1)). Qed.
Lemma lem1312885 (_23374 : nadd) (h1 : term301) : term167 _23374.
Proof. exact (@lem1312843 h1 _23374). Qed.
Lemma lem1312886 (_23374 : nadd) : (term167 _23374) = (nadd_eq _23374 _23374).
Proof. exact (eq_refl (term167 _23374)). Qed.
Lemma lem1312888 (_23375 : nadd) (h1 : term299) : term326 _23375.
Proof. exact (@lem1312871 h1 _23375). Qed.
Lemma lem1312889 (_23375 : nadd) : (term326 _23375) = (term315 _23375).
Proof. exact (eq_refl (term326 _23375)). Qed.
Lemma lem1312890 (_23375 : nadd) (h1 : term299) : term315 _23375.
Proof. exact (EQ_MP (@lem1312889 _23375) (@lem1312888 _23375 h1)). Qed.
Lemma lem1312891 (_23375 : nadd) (_23376 : nadd) (h1 : term299) : term327 _23375 _23376.
Proof. exact (@lem1312890 _23375 h1 _23376). Qed.
Lemma lem1312892 (_23375 : nadd) (_23376 : nadd) : (term327 _23375 _23376) = (term313 _23375 _23376).
Proof. exact (eq_refl (term327 _23375 _23376)). Qed.
Lemma lem1312893 (_23375 : nadd) (_23376 : nadd) (h1 : term299) : term313 _23375 _23376.
Proof. exact (EQ_MP (@lem1312892 _23375 _23376) (@lem1312891 _23375 _23376 h1)). Qed.
Lemma lem1312894 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (h1 : term299) : term328 _23375 _23376 _23377.
Proof. exact (@lem1312893 _23375 _23376 h1 _23377). Qed.
Lemma lem1312895 (_23375 : nadd) (_23377 : nadd) (_23376 : nadd) : (term328 _23375 _23376 _23377) = (term311 _23375 _23377 _23376).
Proof. exact (eq_refl (term328 _23375 _23376 _23377)). Qed.
Lemma lem1312896 (_23375 : nadd) (_23377 : nadd) (_23376 : nadd) (h1 : term299) : term311 _23375 _23377 _23376.
Proof. exact (EQ_MP (@lem1312895 _23375 _23377 _23376) (@lem1312894 _23375 _23376 _23377 h1)). Qed.
Lemma lem1312897 (_23375 : nadd) (_23377 : nadd) (_23376 : nadd) (_23378 : nadd) (h1 : term299) : term329 _23375 _23377 _23376 _23378.
Proof. exact (@lem1312896 _23375 _23377 _23376 h1 _23378). Qed.
Lemma lem1312898 (_23375 : nadd) (_23377 : nadd) (_23376 : nadd) (_23378 : nadd) : (term329 _23375 _23377 _23376 _23378) = (term308 _23375 _23377 _23376 _23378).
Proof. exact (eq_refl (term329 _23375 _23377 _23376 _23378)). Qed.
Lemma lem1312899 (_23375 : nadd) (_23377 : nadd) (_23376 : nadd) (_23378 : nadd) (h1 : term299) : term308 _23375 _23377 _23376 _23378.
Proof. exact (EQ_MP (@lem1312898 _23375 _23377 _23376 _23378) (@lem1312897 _23375 _23377 _23376 _23378 h1)). Qed.
Lemma lem1312900 (_23379 : nadd) (h1 : term266) : term330 _23379.
Proof. exact (@lem1312884 h1 _23379). Qed.
Lemma lem1312901 (_23379 : nadd) : (term330 _23379) = (term323 _23379).
Proof. exact (eq_refl (term330 _23379)). Qed.
Lemma lem1312906 (x : nadd) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1312910 (x : nadd) (y : nadd) (h1 : term259 x y) : term259 x y.
Proof. exact (h1). Qed.
Lemma lem1312923 (_23375 : nadd) (_23377 : nadd) (_23376 : nadd) (_23378 : nadd) : (term308 _23375 _23377 _23376 _23378) = (term331 _23375 _23377 _23376 _23378).
Proof. exact (@lem1309118 (term132 _23375 _23376) (term132 _23377 _23378) (term304 _23375 _23377 _23376 _23378)). Qed.
Lemma lem1312924 (_23375 : nadd) (_23377 : nadd) (_23376 : nadd) (_23378 : nadd) (h1 : term299) : term331 _23375 _23377 _23376 _23378.
Proof. exact (EQ_MP (@lem1312923 _23375 _23377 _23376 _23378) (@lem1312899 _23375 _23377 _23376 _23378 h1)). Qed.
Lemma lem1312930 (_23379 : nadd) (h1 : term266) : term323 _23379.
Proof. exact (EQ_MP (@lem1312901 _23379) (@lem1312900 _23379 h1)). Qed.
Lemma lem1312932 (_23374 : nadd) (h1 : term301) : nadd_eq _23374 _23374.
Proof. exact (EQ_MP (@lem1312886 _23374) (@lem1312885 _23374 h1)). Qed.
Lemma lem1312933 (y : nadd) (h1 : term301) : term332 y.
Proof. exact (@lem1312932 (nadd_inv y) h1). Qed.
Lemma lem1312934 (y : nadd) (h1 : term301) : term333 y.
Proof. exact (fun h0 : term334 y => @lem1312933 y h1). Qed.
Lemma lem1312936 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1312937 (y : nadd) : (term333 y) = (term332 y).
Proof. exact (@lem1312936 (term332 y)). Qed.
Lemma lem1312938 (y : nadd) (h1 : term301) : term332 y.
Proof. exact (EQ_MP (@lem1312937 y) (@lem1312934 y h1)). Qed.
Lemma lem1312940 (x : nadd) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1312941 (x : nadd) (h1 : term27 x) : term335 x.
Proof. exact (fun h0 : term25 x => @lem1312940 x h1). Qed.
Lemma lem1312943 (p : Prop) : (term336 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1312944 (x : nadd) : (term335 x) = (term27 x).
Proof. exact (@lem1312943 (term25 x)). Qed.
Lemma lem1312945 (x : nadd) (h1 : term27 x) : term27 x.
Proof. exact (EQ_MP (@lem1312944 x) (@lem1312941 x h1)). Qed.
Lemma lem1312956 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1312957 (_23379 : nadd) : (term337 _23379) = (term323 _23379).
Proof. exact (@lem1312956 (term25 _23379) (term319 _23379)). Qed.
Lemma lem1312963 (_23379 : nadd) : (term338 _23379) = (term338 _23379).
Proof. exact (eq_refl (term338 _23379)). Qed.
Lemma lem1312964 (_23379 : nadd) : ((term323 _23379) = (term337 _23379)) = ((term323 _23379) = (term323 _23379)).
Proof. exact (MK_COMB (@lem1312963 _23379) (@lem1312957 _23379)). Qed.
Lemma lem1312966 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1312967 (x : Prop) : (x = x) = True.
Proof. exact (@lem1312966 Prop x). Qed.
Lemma lem1312968 (_23379 : nadd) : ((term323 _23379) = (term323 _23379)) = True.
Proof. exact (@lem1312967 (term323 _23379)). Qed.
Lemma lem1312969 (_23379 : nadd) : ((term323 _23379) = (term337 _23379)) = True.
Proof. exact (TRANS (@lem1312964 _23379) (@lem1312968 _23379)). Qed.
Lemma lem1312970 (_23379 : nadd) : True = ((term323 _23379) = (term337 _23379)).
Proof. exact (SYM (@lem1312969 _23379)). Qed.
Lemma lem1312971 (_23379 : nadd) : (term323 _23379) = (term337 _23379).
Proof. exact (EQ_MP (@lem1312970 _23379) (@lem0)). Qed.
Lemma lem1312972 (_23379 : nadd) (h1 : term266) : term337 _23379.
Proof. exact (EQ_MP (@lem1312971 _23379) (@lem1312930 _23379 h1)). Qed.
Lemma lem1312974 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1312977 (_23379 : nadd) : (term337 _23379) = (term289 _23379).
Proof. exact (@lem1312974 (term25 _23379) (term319 _23379)). Qed.
Lemma lem1312980 (_23379 : nadd) (h1 : term266) : term289 _23379.
Proof. exact (EQ_MP (@lem1312977 _23379) (@lem1312972 _23379 h1)). Qed.
Lemma lem1312981 (x : nadd) (h1 : term266) : term289 x.
Proof. exact (@lem1312980 x h1). Qed.
Lemma lem1312984 (x : nadd) (h1 : term266) (h2 : term27 x) : term319 x.
Proof. exact (@lem1312981 x h1 (@lem1312945 x h2)). Qed.
Lemma lem1312985 (x : nadd) (h1 : term266) (h2 : term27 x) : term339 x.
Proof. exact (fun h0 : term340 x => @lem1312984 x h1 h2). Qed.
Lemma lem1312987 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1312988 (x : nadd) : (term339 x) = (term319 x).
Proof. exact (@lem1312987 (term319 x)). Qed.
Lemma lem1312989 (x : nadd) (h1 : term266) (h2 : term27 x) : term319 x.
Proof. exact (EQ_MP (@lem1312988 x) (@lem1312985 x h1 h2)). Qed.
Lemma lem1313005 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1313006 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : (term341 _23375 _23377 _23376 _23378) = (term342 _23375 _23376 _23377 _23378).
Proof. exact (@lem1313005 (term304 _23375 _23377 _23376 _23378) (term132 _23377 _23378)). Qed.
Lemma lem1313012 (_23375 : nadd) (_23376 : nadd) : (term146 _23375 _23376) = (term146 _23375 _23376).
Proof. exact (eq_refl (term146 _23375 _23376)). Qed.
Lemma lem1313013 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : (term331 _23375 _23377 _23376 _23378) = (term343 _23375 _23376 _23377 _23378).
Proof. exact (MK_COMB (@lem1313012 _23375 _23376) (@lem1313006 _23375 _23376 _23377 _23378)). Qed.
Lemma lem1313017 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1313018 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : (term343 _23375 _23376 _23377 _23378) = (term344 _23375 _23376 _23377 _23378).
Proof. exact (@lem1313017 (term304 _23375 _23377 _23376 _23378) (term132 _23375 _23376) (term132 _23377 _23378)). Qed.
Lemma lem1313034 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : (term331 _23375 _23377 _23376 _23378) = (term344 _23375 _23376 _23377 _23378).
Proof. exact (TRANS (@lem1313013 _23375 _23376 _23377 _23378) (@lem1313018 _23375 _23376 _23377 _23378)). Qed.
Lemma lem1313035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1313036 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : (term345 _23375 _23377 _23376 _23378) = (term346 _23375 _23376 _23377 _23378).
Proof. exact (MK_COMB (@lem1313035) (@lem1313034 _23375 _23376 _23377 _23378)). Qed.
Lemma lem1313052 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : (term344 _23375 _23376 _23377 _23378) = (term344 _23375 _23376 _23377 _23378).
Proof. exact (eq_refl (term344 _23375 _23376 _23377 _23378)). Qed.
Lemma lem1313053 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : ((term331 _23375 _23377 _23376 _23378) = (term344 _23375 _23376 _23377 _23378)) = ((term344 _23375 _23376 _23377 _23378) = (term344 _23375 _23376 _23377 _23378)).
Proof. exact (MK_COMB (@lem1313036 _23375 _23376 _23377 _23378) (@lem1313052 _23375 _23376 _23377 _23378)). Qed.
Lemma lem1313055 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1313056 (x : Prop) : (x = x) = True.
Proof. exact (@lem1313055 Prop x). Qed.
Lemma lem1313057 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : ((term344 _23375 _23376 _23377 _23378) = (term344 _23375 _23376 _23377 _23378)) = True.
Proof. exact (@lem1313056 (term344 _23375 _23376 _23377 _23378)). Qed.
Lemma lem1313058 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : ((term331 _23375 _23377 _23376 _23378) = (term344 _23375 _23376 _23377 _23378)) = True.
Proof. exact (TRANS (@lem1313053 _23375 _23376 _23377 _23378) (@lem1313057 _23375 _23376 _23377 _23378)). Qed.
Lemma lem1313059 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : True = ((term331 _23375 _23377 _23376 _23378) = (term344 _23375 _23376 _23377 _23378)).
Proof. exact (SYM (@lem1313058 _23375 _23376 _23377 _23378)). Qed.
Lemma lem1313060 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : (term331 _23375 _23377 _23376 _23378) = (term344 _23375 _23376 _23377 _23378).
Proof. exact (EQ_MP (@lem1313059 _23375 _23376 _23377 _23378) (@lem0)). Qed.
Lemma lem1313061 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) (h1 : term299) : term344 _23375 _23376 _23377 _23378.
Proof. exact (EQ_MP (@lem1313060 _23375 _23376 _23377 _23378) (@lem1312924 _23375 _23377 _23376 _23378 h1)). Qed.
Lemma lem1313063 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1313064 (_23375 : nadd) (_23377 : nadd) (_23376 : nadd) (_23378 : nadd) : (term344 _23375 _23376 _23377 _23378) = (term347 _23375 _23377 _23376 _23378).
Proof. exact (@lem1313063 (term303 _23375 _23376 _23377 _23378) (term304 _23375 _23377 _23376 _23378)). Qed.
Lemma lem1313066 (a : Prop) (b : Prop) : (term152 a b) = (term153 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1313067 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : (term348 _23375 _23376 _23377 _23378) = (term349 _23375 _23376 _23377 _23378).
Proof. exact (@lem1313066 (term132 _23375 _23376) (term132 _23377 _23378)). Qed.
Lemma lem1313069 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1313070 (_23375 : nadd) (_23376 : nadd) : (term140 _23375 _23376) = (nadd_eq _23375 _23376).
Proof. exact (@lem1313069 (nadd_eq _23375 _23376)). Qed.
Lemma lem1313071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1313072 (_23375 : nadd) (_23376 : nadd) : (term156 _23375 _23376) = (term157 _23375 _23376).
Proof. exact (MK_COMB (@lem1313071) (@lem1313070 _23375 _23376)). Qed.
Lemma lem1313074 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1313075 (_23377 : nadd) (_23378 : nadd) : (term140 _23377 _23378) = (nadd_eq _23377 _23378).
Proof. exact (@lem1313074 (nadd_eq _23377 _23378)). Qed.
Lemma lem1313076 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : (term349 _23375 _23376 _23377 _23378) = (term309 _23375 _23376 _23377 _23378).
Proof. exact (MK_COMB (@lem1313072 _23375 _23376) (@lem1313075 _23377 _23378)). Qed.
Lemma lem1313077 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : (term348 _23375 _23376 _23377 _23378) = (term309 _23375 _23376 _23377 _23378).
Proof. exact (TRANS (@lem1313067 _23375 _23376 _23377 _23378) (@lem1313076 _23375 _23376 _23377 _23378)). Qed.
Lemma lem1313078 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1313079 (_23375 : nadd) (_23376 : nadd) (_23377 : nadd) (_23378 : nadd) : (term350 _23375 _23376 _23377 _23378) = (term351 _23375 _23376 _23377 _23378).
Proof. exact (MK_COMB (@lem1313078) (@lem1313077 _23375 _23376 _23377 _23378)). Qed.
Lemma lem1313080 (_23375 : nadd) (_23377 : nadd) (_23376 : nadd) (_23378 : nadd) : (term304 _23375 _23377 _23376 _23378) = (term304 _23375 _23377 _23376 _23378).
Proof. exact (eq_refl (term304 _23375 _23377 _23376 _23378)). Qed.
Lemma lem1313081 (_23375 : nadd) (_23377 : nadd) (_23376 : nadd) (_23378 : nadd) : (term347 _23375 _23377 _23376 _23378) = (term291 _23375 _23377 _23376 _23378).
Proof. exact (MK_COMB (@lem1313079 _23375 _23376 _23377 _23378) (@lem1313080 _23375 _23377 _23376 _23378)). Qed.
Lemma lem1313082 (_23375 : nadd) (_23377 : nadd) (_23376 : nadd) (_23378 : nadd) : (term344 _23375 _23376 _23377 _23378) = (term291 _23375 _23377 _23376 _23378).
Proof. exact (TRANS (@lem1313064 _23375 _23377 _23376 _23378) (@lem1313081 _23375 _23377 _23376 _23378)). Qed.
Lemma lem1313084 (y : nadd) (x : nadd) (h1 : term266) (h2 : term301) (h3 : term27 x) : term352 y x.
Proof. exact (conj (@lem1312938 y h2) (@lem1312989 x h1 h3)). Qed.
Lemma lem1313086 (_23375 : nadd) (_23377 : nadd) (_23376 : nadd) (_23378 : nadd) (h1 : term299) : term291 _23375 _23377 _23376 _23378.
Proof. exact (EQ_MP (@lem1313082 _23375 _23377 _23376 _23378) (@lem1313061 _23375 _23376 _23377 _23378 h1)). Qed.
Lemma lem1313087 (x : nadd) (y : nadd) (h1 : term299) : term353 x y.
Proof. exact (@lem1313086 (nadd_inv y) (term354 x) (nadd_inv y) term242 h1). Qed.
Lemma lem1313090 (y : nadd) (x : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) : term257 x y.
Proof. exact (@lem1313087 x y h1 (@lem1313084 y x h2 h3 h4)). Qed.
Lemma lem1313091 (y : nadd) (x : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) : term355 x y.
Proof. exact (fun h0 : term259 x y => @lem1313090 y x h1 h2 h3 h4). Qed.
Lemma lem1313093 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1313094 (x : nadd) (y : nadd) : (term355 x y) = (term257 x y).
Proof. exact (@lem1313093 (term257 x y)). Qed.
Lemma lem1313095 (y : nadd) (x : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) : term257 x y.
Proof. exact (EQ_MP (@lem1313094 x y) (@lem1313091 y x h1 h2 h3 h4)). Qed.
Lemma lem1313098 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1313100 (x : nadd) (y : nadd) : (term259 x y) = (term356 x y).
Proof. exact (@lem1313098 (term257 x y)). Qed.
Lemma lem1313103 (x : nadd) (y : nadd) (h1 : term259 x y) : term356 x y.
Proof. exact (EQ_MP (@lem1313100 x y) (@lem1312910 x y h1)). Qed.
Lemma lem1313106 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (@lem1313103 x y h5 (@lem1313095 y x h1 h2 h3 h4)). Qed.
Lemma lem1313107 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : term164.
Proof. exact (fun h0 : ~ False => @lem1313106 x y h1 h2 h3 h4 h5). Qed.
Lemma lem1313109 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1313110 : term164 = False.
Proof. exact (@lem1313109 False). Qed.
Lemma lem1313111 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313110) (@lem1313107 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1313112 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : (term259 x y) = False.
Proof. exact (prop_ext (fun h6 : term259 x y => @lem1313111 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1312910 x y h5)). Qed.
Lemma lem1313113 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313112 x y h1 h2 h3 h4 h5) (@lem1312910 x y h5)). Qed.
Lemma lem1313114 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : (term27 x) = False.
Proof. exact (prop_ext (fun h6 : term27 x => @lem1313113 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1312906 x h4)). Qed.
Lemma lem1313115 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313114 x y h1 h2 h3 h4 h5) (@lem1312906 x h4)). Qed.
Lemma lem1313116 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : (term259 x y) = False.
Proof. exact (prop_ext (fun h6 : term259 x y => @lem1313115 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1312836 x y h5)). Qed.
Lemma lem1313117 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313116 x y h1 h2 h3 h4 h5) (@lem1312836 x y h5)). Qed.
Lemma lem1313118 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : (term27 x) = False.
Proof. exact (prop_ext (fun h6 : term27 x => @lem1313117 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1312828 x h4)). Qed.
Lemma lem1313119 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313118 x y h1 h2 h3 h4 h5) (@lem1312828 x h4)). Qed.
Lemma lem1313120 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : term301 = False.
Proof. exact (prop_ext (fun h6 : term301 => @lem1313119 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1312843 h3)). Qed.
Lemma lem1313121 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313120 x y h1 h2 h3 h4 h5) (@lem1312843 h3)). Qed.
Lemma lem1313122 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : (term259 x y) = False.
Proof. exact (prop_ext (fun h6 : term259 x y => @lem1313121 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1312836 x y h5)). Qed.
Lemma lem1313123 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313122 x y h1 h2 h3 h4 h5) (@lem1312836 x y h5)). Qed.
Lemma lem1313124 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : (term27 x) = False.
Proof. exact (prop_ext (fun h6 : term27 x => @lem1313123 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1312828 x h4)). Qed.
Lemma lem1313125 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313124 x y h1 h2 h3 h4 h5) (@lem1312828 x h4)). Qed.
Lemma lem1313126 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : term301 = False.
Proof. exact (prop_ext (fun h6 : term301 => @lem1313125 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1312741 h3)). Qed.
Lemma lem1313127 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313126 x y h1 h2 h3 h4 h5) (@lem1312741 h3)). Qed.
Lemma lem1313128 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : (term259 x y) = False.
Proof. exact (prop_ext (fun h6 : term259 x y => @lem1313127 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1312732 x y h5)). Qed.
Lemma lem1313129 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313128 x y h1 h2 h3 h4 h5) (@lem1312732 x y h5)). Qed.
Lemma lem1313130 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : (term27 x) = False.
Proof. exact (prop_ext (fun h6 : term27 x => @lem1313129 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1312688 x h4)). Qed.
Lemma lem1313131 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313130 x y h1 h2 h3 h4 h5) (@lem1312688 x h4)). Qed.
Lemma lem1313132 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : term301 = False.
Proof. exact (prop_ext (fun h6 : term301 => @lem1313131 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1312515 h3)). Qed.
Lemma lem1313133 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313132 x y h1 h2 h3 h4 h5) (@lem1312515 h3)). Qed.
Lemma lem1313134 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : (term259 x y) = False.
Proof. exact (prop_ext (fun h6 : term259 x y => @lem1313133 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1312502 x y h5)). Qed.
Lemma lem1313135 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313134 x y h1 h2 h3 h4 h5) (@lem1312502 x y h5)). Qed.
Lemma lem1313136 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : (term27 x) = False.
Proof. exact (prop_ext (fun h6 : term27 x => @lem1313135 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1312490 x h4)). Qed.
Lemma lem1313137 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 x) (h5 : term259 x y) : False.
Proof. exact (EQ_MP (@lem1313136 x y h1 h2 h3 h4 h5) (@lem1312490 x h4)). Qed.
Lemma lem1313138 (x : nadd) (y : nadd) (h1 : term299) (h2 : term301) (h3 : term27 x) (h4 : term259 x y) : term264.
Proof. exact (fun h0 : term266 => @lem1313137 x y h1 h0 h2 h3 h4). Qed.
Lemma lem1313139 : term264 = term265.
Proof. exact (@lem69 term266). Qed.
Lemma lem1313140 (x : nadd) (y : nadd) (h1 : term299) (h2 : term301) (h3 : term27 x) (h4 : term259 x y) : term265.
Proof. exact (EQ_MP (@lem1313139) (@lem1313138 x y h1 h2 h3 h4)). Qed.
Lemma lem1313141 (x : nadd) (y : nadd) (h1 : term301) (h2 : term27 x) (h3 : term259 x y) : term269.
Proof. exact (fun h0 : term299 => @lem1313140 x y h0 h1 h2 h3). Qed.
Lemma lem1313142 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term259 x y) : term272.
Proof. exact (fun h0 : term301 => @lem1313141 x y h0 h1 h2). Qed.
Lemma lem1313143 (y : nadd) (x : nadd) (h1 : term27 x) : term275 x y.
Proof. exact (fun h0 : term259 x y => @lem1313142 x y h1 h0). Qed.
Lemma lem1313144 (y : nadd) (x : nadd) (h1 : term27 x) : term277 x y.
Proof. exact (fun h0 : term27 y => @lem1313143 y x h1). Qed.
Lemma lem1313145 (x : nadd) (y : nadd) : term279 x y.
Proof. exact (fun h0 : term27 x => @lem1313144 y x h0). Qed.
Lemma lem1313146 (x : nadd) (y : nadd) : term280 x y.
Proof. exact (fun h0 : nadd_eq x y => @lem1313145 x y). Qed.
Lemma lem1313151 (y : nadd) : term284 y.
Proof. exact (fun x : nadd => @lem1313146 x y). Qed.
Lemma lem1313156 : term288.
Proof. exact (fun y : nadd => @lem1313151 y). Qed.
Lemma lem1313157 : term287.
Proof. exact (EQ_MP (@lem1312471) (@lem1313156)). Qed.
Lemma lem1313158 (y : nadd) : term357 y.
Proof. exact (@lem1313157 y). Qed.
Lemma lem1313159 (y : nadd) : (term357 y) = (term283 y).
Proof. exact (eq_refl (term357 y)). Qed.
Lemma lem1313160 (y : nadd) : term283 y.
Proof. exact (EQ_MP (@lem1313159 y) (@lem1313158 y)). Qed.
Lemma lem1313161 (y : nadd) (x : nadd) : term358 y x.
Proof. exact (@lem1313160 y x). Qed.
Lemma lem1313162 (x : nadd) (y : nadd) : (term358 y x) = (term260 x y).
Proof. exact (eq_refl (term358 y x)). Qed.
Lemma lem1313163 (x : nadd) (y : nadd) : term260 x y.
Proof. exact (EQ_MP (@lem1313162 x y) (@lem1313161 y x)). Qed.
Lemma lem1313165 (x : nadd) (y : nadd) : term260 x y.
Proof. exact (@lem1312235 x y (@lem1313163 x y)). Qed.
Lemma lem1313166 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term278 x y.
Proof. exact (@lem1313165 x y (@lem1309210 x y h1)). Qed.
Lemma lem1313167 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) : term276 x y.
Proof. exact (@lem1313166 x y h2 (@lem1309209 x h1)). Qed.
Lemma lem1313168 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term274 x y.
Proof. exact (@lem1313167 x y h1 h3 (@lem1310360 y h2)). Qed.
Lemma lem1313169 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term259 x y) (h4 : nadd_eq x y) : term271.
Proof. exact (@lem1313168 x y h1 h2 h4 (@lem1312220 x y h3)). Qed.
Lemma lem1313170 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term259 x y) (h4 : nadd_eq x y) : term268.
Proof. exact (@lem1313169 x y h1 h2 h3 h4 (@lem1267990)). Qed.
Lemma lem1313171 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term259 x y) (h4 : nadd_eq x y) : term264.
Proof. exact (@lem1313170 x y h1 h2 h3 h4 (@lem1279298)). Qed.
Lemma lem1313172 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term259 x y) (h4 : nadd_eq x y) : False.
Proof. exact (@lem1313171 x y h1 h2 h3 h4 (@lem1308984)). Qed.
Lemma lem1313173 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term259 x y) (h4 : nadd_eq x y) : (term259 x y) = False.
Proof. exact (prop_ext (fun h5 : term259 x y => @lem1313172 x y h1 h2 h3 h4) (fun h5 : False => @lem1312220 x y h3)). Qed.
Lemma lem1313174 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term259 x y) (h4 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1313173 x y h1 h2 h3 h4) (@lem1312220 x y h3)). Qed.
Lemma lem1313175 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term258 x y.
Proof. exact (fun h0 : term259 x y => @lem1313174 x y h1 h2 h0 h3). Qed.
Lemma lem1313176 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term257 x y.
Proof. exact (EQ_MP (@lem1312219 x y) (@lem1313175 x y h1 h2 h3)). Qed.
Lemma lem1313178 (x : nadd) (z : nadd) : term18 x z.
Proof. exact (EQ_MP (@lem1309107 x z) (@lem1309106 x z)). Qed.
Lemma lem1313179 (y : nadd) (x : nadd) : term359 y x.
Proof. exact (@lem1313178 (nadd_inv x) (term360 y x)). Qed.
Lemma lem1313181 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1313182 (y : nadd) (x : nadd) : (term361 y x) = (term362 y x).
Proof. exact (@lem1313181 (term361 y x)). Qed.
Lemma lem1313183 (y : nadd) (x : nadd) : (term362 y x) = (term361 y x).
Proof. exact (SYM (@lem1313182 y x)). Qed.
Lemma lem1313184 (y : nadd) (x : nadd) (h1 : term363 y x) : term363 y x.
Proof. exact (h1). Qed.
Lemma lem1313187 (y : nadd) (x : nadd) (h1 : term364 y x) : term364 y x.
Proof. exact (h1). Qed.
Lemma lem1313188 (y : nadd) (x : nadd) : term365 y x.
Proof. exact (fun h0 : term364 y x => @lem1313187 y x h0). Qed.
Lemma lem1313189 (y : nadd) (x : nadd) (h1 : term365 y x) : term365 y x.
Proof. exact (h1). Qed.
Lemma lem1313190 (y : nadd) (x : nadd) (h1 : term364 y x) : term364 y x.
Proof. exact (h1). Qed.
Lemma lem1313191 (y : nadd) (x : nadd) (h1 : term365 y x) (h2 : term364 y x) : term364 y x.
Proof. exact (@lem1313189 y x h1 (@lem1313190 y x h2)). Qed.
Lemma lem1313192 (y : nadd) (x : nadd) (h1 : term364 y x) : term366 y x.
Proof. exact (fun h0 : term365 y x => @lem1313191 y x h0 h1). Qed.
Lemma lem1313193 (y : nadd) (x : nadd) (h1 : term365 y x) : term365 y x.
Proof. exact (h1). Qed.
Lemma lem1313194 (y : nadd) (x : nadd) (h1 : term365 y x) (h2 : term364 y x) : term364 y x.
Proof. exact (@lem1313192 y x h2 (@lem1313193 y x h1)). Qed.
Lemma lem1313195 (y : nadd) (x : nadd) (h1 : term365 y x) : term365 y x.
Proof. exact (fun h0 : term364 y x => @lem1313194 y x h1 h0). Qed.
Lemma lem1313196 (y : nadd) (x : nadd) : term367 y x.
Proof. exact (fun h0 : term365 y x => @lem1313195 y x h0). Qed.
Lemma lem1313199 (y : nadd) (x : nadd) : term365 y x.
Proof. exact (@lem1313196 y x (@lem1313188 y x)). Qed.
Lemma lem1313233 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1313234 : term368 = term369.
Proof. exact (@lem1313233 term299). Qed.
Lemma lem1313255 : term270 = term270.
Proof. exact (eq_refl term270). Qed.
Lemma lem1313256 : term370 = term371.
Proof. exact (MK_COMB (@lem1313255) (@lem1313234)). Qed.
Lemma lem1313259 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1313260 : term372 = term373.
Proof. exact (MK_COMB (@lem1313259) (@lem1313256)). Qed.
Lemma lem1313263 (y : nadd) (x : nadd) : (term374 y x) = (term374 y x).
Proof. exact (eq_refl (term374 y x)). Qed.
Lemma lem1313264 (y : nadd) (x : nadd) : (term375 y x) = (term376 y x).
Proof. exact (MK_COMB (@lem1313263 y x) (@lem1313260)). Qed.
Lemma lem1313267 (y : nadd) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem1313268 (y : nadd) (x : nadd) : (term377 y x) = (term378 y x).
Proof. exact (MK_COMB (@lem1313267 y) (@lem1313264 y x)). Qed.
Lemma lem1313271 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1313272 (y : nadd) (x : nadd) : (term379 y x) = (term380 y x).
Proof. exact (MK_COMB (@lem1313271 x) (@lem1313268 y x)). Qed.
Lemma lem1313275 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1313276 (y : nadd) (x : nadd) : (term364 y x) = (term381 y x).
Proof. exact (MK_COMB (@lem1313275 x y) (@lem1313272 y x)). Qed.
Lemma lem1313279 (x : nadd) : (term382 x) = (term383 x).
Proof. exact (fun_ext (fun y : nadd => @lem1313276 y x)). Qed.
Lemma lem1313280 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313281 (x : nadd) : (term384 x) = (term385 x).
Proof. exact (MK_COMB (@lem1313280) (@lem1313279 x)). Qed.
Lemma lem1313286 : term386 = term387.
Proof. exact (fun_ext (fun x : nadd => @lem1313281 x)). Qed.
Lemma lem1313287 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313296 : term388 = term389.
Proof. exact (MK_COMB (@lem1313287) (@lem1313286)). Qed.
Lemma lem1313305 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term291 x y x' y') = (term291 x y x' y').
Proof. exact (eq_refl (term291 x y x' y')). Qed.
Lemma lem1313306 (x : nadd) (y : nadd) (x' : nadd) : (term292 x y x') = (term292 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1313305 x y x' y')). Qed.
Lemma lem1313307 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313308 (x : nadd) (y : nadd) (x' : nadd) : (term293 x y x') = (term293 x y x').
Proof. exact (MK_COMB (@lem1313307) (@lem1313306 x y x')). Qed.
Lemma lem1313309 (x : nadd) (x' : nadd) : (term294 x x') = (term294 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1313308 x y x')). Qed.
Lemma lem1313310 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313311 (x : nadd) (x' : nadd) : (term295 x x') = (term295 x x').
Proof. exact (MK_COMB (@lem1313310) (@lem1313309 x x')). Qed.
Lemma lem1313312 (x : nadd) : (term296 x) = (term296 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1313311 x x')). Qed.
Lemma lem1313313 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313314 (x : nadd) : (term297 x) = (term297 x).
Proof. exact (MK_COMB (@lem1313313) (@lem1313312 x)). Qed.
Lemma lem1313315 : term298 = term298.
Proof. exact (fun_ext (fun x : nadd => @lem1313314 x)). Qed.
Lemma lem1313316 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313317 : term299 = term299.
Proof. exact (MK_COMB (@lem1313316) (@lem1313315)). Qed.
Lemma lem1313318 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1313319 : term369 = term369.
Proof. exact (MK_COMB (@lem1313318) (@lem1313317)). Qed.
Lemma lem1313320 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1313321 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1313320 x)). Qed.
Lemma lem1313322 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313323 : term301 = term301.
Proof. exact (MK_COMB (@lem1313322) (@lem1313321)). Qed.
Lemma lem1313324 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1313325 : term270 = term270.
Proof. exact (MK_COMB (@lem1313324) (@lem1313323)). Qed.
Lemma lem1313326 : term371 = term371.
Proof. exact (MK_COMB (@lem1313325) (@lem1313319)). Qed.
Lemma lem1313331 (y : nadd) (x : nadd) : ((nadd_eq x y) = (nadd_eq y x)) = ((nadd_eq x y) = (nadd_eq y x)).
Proof. exact (eq_refl ((nadd_eq x y) = (nadd_eq y x))). Qed.
Lemma lem1313332 (x : nadd) : (term58 x) = (term58 x).
Proof. exact (fun_ext (fun y : nadd => @lem1313331 y x)). Qed.
Lemma lem1313333 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313334 (x : nadd) : (term59 x) = (term59 x).
Proof. exact (MK_COMB (@lem1313333) (@lem1313332 x)). Qed.
Lemma lem1313335 : term60 = term60.
Proof. exact (fun_ext (fun x : nadd => @lem1313334 x)). Qed.
Lemma lem1313336 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313337 : term61 = term61.
Proof. exact (MK_COMB (@lem1313336) (@lem1313335)). Qed.
Lemma lem1313338 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1313339 : term36 = term36.
Proof. exact (MK_COMB (@lem1313338) (@lem1313337)). Qed.
Lemma lem1313340 : term373 = term373.
Proof. exact (MK_COMB (@lem1313339) (@lem1313326)). Qed.
Lemma lem1313345 (y : nadd) (x : nadd) : (term374 y x) = (term374 y x).
Proof. exact (eq_refl (term374 y x)). Qed.
Lemma lem1313346 (y : nadd) (x : nadd) : (term376 y x) = (term376 y x).
Proof. exact (MK_COMB (@lem1313345 y x) (@lem1313340)). Qed.
Lemma lem1313351 (y : nadd) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem1313352 (y : nadd) (x : nadd) : (term378 y x) = (term378 y x).
Proof. exact (MK_COMB (@lem1313351 y) (@lem1313346 y x)). Qed.
Lemma lem1313357 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1313358 (y : nadd) (x : nadd) : (term380 y x) = (term380 y x).
Proof. exact (MK_COMB (@lem1313357 x) (@lem1313352 y x)). Qed.
Lemma lem1313361 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1313362 (y : nadd) (x : nadd) : (term381 y x) = (term381 y x).
Proof. exact (MK_COMB (@lem1313361 x y) (@lem1313358 y x)). Qed.
Lemma lem1313363 (x : nadd) : (term383 x) = (term383 x).
Proof. exact (fun_ext (fun y : nadd => @lem1313362 y x)). Qed.
Lemma lem1313364 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313365 (x : nadd) : (term385 x) = (term385 x).
Proof. exact (MK_COMB (@lem1313364) (@lem1313363 x)). Qed.
Lemma lem1313366 : term387 = term387.
Proof. exact (fun_ext (fun x : nadd => @lem1313365 x)). Qed.
Lemma lem1313367 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313368 : term389 = term389.
Proof. exact (MK_COMB (@lem1313367) (@lem1313366)). Qed.
Lemma lem1313441 : term388 = term389.
Proof. exact (TRANS (@lem1313296) (@lem1313368)). Qed.
Lemma lem1313442 : term389 = term388.
Proof. exact (SYM (@lem1313441)). Qed.
Lemma lem1313447 (h1 : term61) : term61.
Proof. exact (h1). Qed.
Lemma lem1313448 (h1 : term301) : term301.
Proof. exact (h1). Qed.
Lemma lem1313449 (h1 : term299) : term299.
Proof. exact (h1). Qed.
Lemma lem1313455 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1313473 (y : nadd) (x : nadd) (h1 : term363 y x) : term363 y x.
Proof. exact (h1). Qed.
Lemma lem1313488 (y : nadd) (x : nadd) : ((nadd_eq x y) = (nadd_eq y x)) = (term62 y x).
Proof. exact (@lem17784 (nadd_eq x y) (nadd_eq y x)). Qed.
Lemma lem1313489 (x : nadd) : (term58 x) = (term63 x).
Proof. exact (fun_ext (fun y : nadd => @lem1313488 y x)). Qed.
Lemma lem1313490 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313491 (x : nadd) : (term59 x) = (term64 x).
Proof. exact (MK_COMB (@lem1313490) (@lem1313489 x)). Qed.
Lemma lem1313492 : term60 = term65.
Proof. exact (fun_ext (fun x : nadd => @lem1313491 x)). Qed.
Lemma lem1313493 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313494 : term61 = term66.
Proof. exact (MK_COMB (@lem1313493) (@lem1313492)). Qed.
Lemma lem1313500 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1313501 (P : nadd -> Prop) (Q : nadd -> Prop) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem1313500 nadd P Q). Qed.
Lemma lem1313502 (x : nadd) : (term71 x) = (term72 x).
Proof. exact (@lem1313501 (term73 x) (term74 x)). Qed.
Lemma lem1313503 (y : nadd) (x : nadd) : (term75 x y) = (term76 y x).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1313504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1313505 (y : nadd) (x : nadd) : (term77 x y) = (term78 y x).
Proof. exact (MK_COMB (@lem1313504) (@lem1313503 y x)). Qed.
Lemma lem1313506 (y : nadd) (x : nadd) : (term79 x y) = (term80 y x).
Proof. exact (eq_refl (term79 x y)). Qed.
Lemma lem1313507 (y : nadd) (x : nadd) : (term81 x y) = (term62 y x).
Proof. exact (MK_COMB (@lem1313505 y x) (@lem1313506 y x)). Qed.
Lemma lem1313508 (x : nadd) : (term82 x) = (term63 x).
Proof. exact (fun_ext (fun y : nadd => @lem1313507 y x)). Qed.
Lemma lem1313509 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313510 (x : nadd) : (term71 x) = (term64 x).
Proof. exact (MK_COMB (@lem1313509) (@lem1313508 x)). Qed.
Lemma lem1313511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1313512 (x : nadd) : (term83 x) = (term84 x).
Proof. exact (MK_COMB (@lem1313511) (@lem1313510 x)). Qed.
Lemma lem1313513 (y : nadd) (x : nadd) : (term75 x y) = (term76 y x).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1313514 (x : nadd) : (term85 x) = (term73 x).
Proof. exact (fun_ext (fun y : nadd => @lem1313513 y x)). Qed.
Lemma lem1313515 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313516 (x : nadd) : (term86 x) = (term87 x).
Proof. exact (MK_COMB (@lem1313515) (@lem1313514 x)). Qed.
Lemma lem1313517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1313518 (x : nadd) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem1313517) (@lem1313516 x)). Qed.
Lemma lem1313519 (y : nadd) (x : nadd) : (term79 x y) = (term80 y x).
Proof. exact (eq_refl (term79 x y)). Qed.
Lemma lem1313520 (x : nadd) : (term90 x) = (term74 x).
Proof. exact (fun_ext (fun y : nadd => @lem1313519 y x)). Qed.
Lemma lem1313521 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313522 (x : nadd) : (term91 x) = (term92 x).
Proof. exact (MK_COMB (@lem1313521) (@lem1313520 x)). Qed.
Lemma lem1313523 (x : nadd) : (term72 x) = (term93 x).
Proof. exact (MK_COMB (@lem1313518 x) (@lem1313522 x)). Qed.
Lemma lem1313524 (x : nadd) : ((term71 x) = (term72 x)) = ((term64 x) = (term93 x)).
Proof. exact (MK_COMB (@lem1313512 x) (@lem1313523 x)). Qed.
Lemma lem1313525 (x : nadd) : (term64 x) = (term93 x).
Proof. exact (EQ_MP (@lem1313524 x) (@lem1313502 x)). Qed.
Lemma lem1313622 : term65 = term94.
Proof. exact (fun_ext (fun x : nadd => @lem1313525 x)). Qed.
Lemma lem1313623 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313624 : term66 = term95.
Proof. exact (MK_COMB (@lem1313623) (@lem1313622)). Qed.
Lemma lem1313626 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1313627 (P : nadd -> Prop) (Q : nadd -> Prop) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem1313626 nadd P Q). Qed.
Lemma lem1313628 : term96 = term97.
Proof. exact (@lem1313627 term98 term99). Qed.
Lemma lem1313629 (x : nadd) : (term100 x) = (term87 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1313630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1313631 (x : nadd) : (term101 x) = (term89 x).
Proof. exact (MK_COMB (@lem1313630) (@lem1313629 x)). Qed.
Lemma lem1313632 (x : nadd) : (term102 x) = (term92 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1313633 (x : nadd) : (term103 x) = (term93 x).
Proof. exact (MK_COMB (@lem1313631 x) (@lem1313632 x)). Qed.
Lemma lem1313634 : term104 = term94.
Proof. exact (fun_ext (fun x : nadd => @lem1313633 x)). Qed.
Lemma lem1313635 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313636 : term96 = term95.
Proof. exact (MK_COMB (@lem1313635) (@lem1313634)). Qed.
Lemma lem1313637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1313638 : term105 = term106.
Proof. exact (MK_COMB (@lem1313637) (@lem1313636)). Qed.
Lemma lem1313639 (x : nadd) : (term100 x) = (term87 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1313640 : term107 = term98.
Proof. exact (fun_ext (fun x : nadd => @lem1313639 x)). Qed.
Lemma lem1313641 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313642 : term108 = term109.
Proof. exact (MK_COMB (@lem1313641) (@lem1313640)). Qed.
Lemma lem1313643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1313644 : term110 = term111.
Proof. exact (MK_COMB (@lem1313643) (@lem1313642)). Qed.
Lemma lem1313645 (x : nadd) : (term102 x) = (term92 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1313646 : term112 = term99.
Proof. exact (fun_ext (fun x : nadd => @lem1313645 x)). Qed.
Lemma lem1313647 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313648 : term113 = term114.
Proof. exact (MK_COMB (@lem1313647) (@lem1313646)). Qed.
Lemma lem1313649 : term97 = term115.
Proof. exact (MK_COMB (@lem1313644) (@lem1313648)). Qed.
Lemma lem1313650 : (term96 = term97) = (term95 = term115).
Proof. exact (MK_COMB (@lem1313638) (@lem1313649)). Qed.
Lemma lem1313651 : term95 = term115.
Proof. exact (EQ_MP (@lem1313650) (@lem1313628)). Qed.
Lemma lem1313758 : term66 = term115.
Proof. exact (TRANS (@lem1313624) (@lem1313651)). Qed.
Lemma lem1313759 : term61 = term115.
Proof. exact (TRANS (@lem1313494) (@lem1313758)). Qed.
Lemma lem1313760 (h1 : term61) : term115.
Proof. exact (EQ_MP (@lem1313759) (@lem1313447 h1)). Qed.
Lemma lem1313761 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1313762 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1313761 x)). Qed.
Lemma lem1313763 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313772 : term301 = term301.
Proof. exact (MK_COMB (@lem1313763) (@lem1313762)). Qed.
Lemma lem1313773 (h1 : term301) : term301.
Proof. exact (EQ_MP (@lem1313772) (@lem1313448 h1)). Qed.
Lemma lem1313780 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term302 x x' y y') = (term303 x x' y y').
Proof. exact (@lem17045 (nadd_eq x x') (nadd_eq y y')). Qed.
Lemma lem1313781 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term304 x y x' y') = (term304 x y x' y').
Proof. exact (eq_refl (term304 x y x' y')). Qed.
Lemma lem1313782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1313783 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term305 x x' y y') = (term306 x x' y y').
Proof. exact (MK_COMB (@lem1313782) (@lem1313780 x x' y y')). Qed.
Lemma lem1313784 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term307 x y x' y') = (term308 x y x' y').
Proof. exact (MK_COMB (@lem1313783 x x' y y') (@lem1313781 x y x' y')). Qed.
Lemma lem1313785 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term291 x y x' y') = (term307 x y x' y').
Proof. exact (@lem17265 (term309 x x' y y') (term304 x y x' y')). Qed.
Lemma lem1313786 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term291 x y x' y') = (term308 x y x' y').
Proof. exact (TRANS (@lem1313785 x y x' y') (@lem1313784 x y x' y')). Qed.
Lemma lem1313787 (x : nadd) (y : nadd) (x' : nadd) : (term292 x y x') = (term310 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1313786 x y x' y')). Qed.
Lemma lem1313788 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313789 (x : nadd) (y : nadd) (x' : nadd) : (term293 x y x') = (term311 x y x').
Proof. exact (MK_COMB (@lem1313788) (@lem1313787 x y x')). Qed.
Lemma lem1313790 (x : nadd) (x' : nadd) : (term294 x x') = (term312 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1313789 x y x')). Qed.
Lemma lem1313791 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313792 (x : nadd) (x' : nadd) : (term295 x x') = (term313 x x').
Proof. exact (MK_COMB (@lem1313791) (@lem1313790 x x')). Qed.
Lemma lem1313793 (x : nadd) : (term296 x) = (term314 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1313792 x x')). Qed.
Lemma lem1313794 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313795 (x : nadd) : (term297 x) = (term315 x).
Proof. exact (MK_COMB (@lem1313794) (@lem1313793 x)). Qed.
Lemma lem1313796 : term298 = term316.
Proof. exact (fun_ext (fun x : nadd => @lem1313795 x)). Qed.
Lemma lem1313797 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313862 : term299 = term317.
Proof. exact (MK_COMB (@lem1313797) (@lem1313796)). Qed.
Lemma lem1313863 (h1 : term299) : term317.
Proof. exact (EQ_MP (@lem1313862) (@lem1313449 h1)). Qed.
Lemma lem1313869 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1313925 (y : nadd) (x : nadd) (h1 : term363 y x) : term363 y x.
Proof. exact (h1). Qed.
Lemma lem1313940 (y : nadd) (x : nadd) : (term80 y x) = (term80 y x).
Proof. exact (eq_refl (term80 y x)). Qed.
Lemma lem1313941 (x : nadd) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : nadd => @lem1313940 y x)). Qed.
Lemma lem1313942 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313943 (x : nadd) : (term92 x) = (term92 x).
Proof. exact (MK_COMB (@lem1313942) (@lem1313941 x)). Qed.
Lemma lem1313944 : term99 = term99.
Proof. exact (fun_ext (fun x : nadd => @lem1313943 x)). Qed.
Lemma lem1313945 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313946 : term114 = term114.
Proof. exact (MK_COMB (@lem1313945) (@lem1313944)). Qed.
Lemma lem1313961 (y : nadd) (x : nadd) : (term76 y x) = (term76 y x).
Proof. exact (eq_refl (term76 y x)). Qed.
Lemma lem1313962 (x : nadd) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun y : nadd => @lem1313961 y x)). Qed.
Lemma lem1313963 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313964 (x : nadd) : (term87 x) = (term87 x).
Proof. exact (MK_COMB (@lem1313963) (@lem1313962 x)). Qed.
Lemma lem1313965 : term98 = term98.
Proof. exact (fun_ext (fun x : nadd => @lem1313964 x)). Qed.
Lemma lem1313966 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313967 : term109 = term109.
Proof. exact (MK_COMB (@lem1313966) (@lem1313965)). Qed.
Lemma lem1313968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1313969 : term111 = term111.
Proof. exact (MK_COMB (@lem1313968) (@lem1313967)). Qed.
Lemma lem1313970 : term115 = term115.
Proof. exact (MK_COMB (@lem1313969) (@lem1313946)). Qed.
Lemma lem1313971 (h1 : term61) : term115.
Proof. exact (EQ_MP (@lem1313970) (@lem1313760 h1)). Qed.
Lemma lem1313976 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1313977 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1313976 x)). Qed.
Lemma lem1313978 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1313979 : term301 = term301.
Proof. exact (MK_COMB (@lem1313978) (@lem1313977)). Qed.
Lemma lem1313980 (h1 : term301) : term301.
Proof. exact (EQ_MP (@lem1313979) (@lem1313773 h1)). Qed.
Lemma lem1314013 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term308 x y x' y') = (term308 x y x' y').
Proof. exact (eq_refl (term308 x y x' y')). Qed.
Lemma lem1314014 (x : nadd) (y : nadd) (x' : nadd) : (term310 x y x') = (term310 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1314013 x y x' y')). Qed.
Lemma lem1314015 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314016 (x : nadd) (y : nadd) (x' : nadd) : (term311 x y x') = (term311 x y x').
Proof. exact (MK_COMB (@lem1314015) (@lem1314014 x y x')). Qed.
Lemma lem1314017 (x : nadd) (x' : nadd) : (term312 x x') = (term312 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1314016 x y x')). Qed.
Lemma lem1314018 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314019 (x : nadd) (x' : nadd) : (term313 x x') = (term313 x x').
Proof. exact (MK_COMB (@lem1314018) (@lem1314017 x x')). Qed.
Lemma lem1314020 (x : nadd) : (term314 x) = (term314 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1314019 x x')). Qed.
Lemma lem1314021 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314022 (x : nadd) : (term315 x) = (term315 x).
Proof. exact (MK_COMB (@lem1314021) (@lem1314020 x)). Qed.
Lemma lem1314023 : term316 = term316.
Proof. exact (fun_ext (fun x : nadd => @lem1314022 x)). Qed.
Lemma lem1314024 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314025 : term317 = term317.
Proof. exact (MK_COMB (@lem1314024) (@lem1314023)). Qed.
Lemma lem1314026 (h1 : term299) : term317.
Proof. exact (EQ_MP (@lem1314025) (@lem1313863 h1)). Qed.
Lemma lem1314027 (h1 : term61) : term114.
Proof. exact (proj2 (@lem1313971 h1)). Qed.
Lemma lem1314032 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1314044 (y : nadd) (x : nadd) (h1 : term363 y x) : term363 y x.
Proof. exact (h1). Qed.
Lemma lem1314046 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1314047 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1314046 x)). Qed.
Lemma lem1314048 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314050 : term301 = term301.
Proof. exact (MK_COMB (@lem1314048) (@lem1314047)). Qed.
Lemma lem1314051 (h1 : term301) : term301.
Proof. exact (EQ_MP (@lem1314050) (@lem1313980 h1)). Qed.
Lemma lem1314065 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term308 x y x' y') = (term308 x y x' y').
Proof. exact (eq_refl (term308 x y x' y')). Qed.
Lemma lem1314066 (x : nadd) (y : nadd) (x' : nadd) : (term310 x y x') = (term310 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1314065 x y x' y')). Qed.
Lemma lem1314067 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314068 (x : nadd) (y : nadd) (x' : nadd) : (term311 x y x') = (term311 x y x').
Proof. exact (MK_COMB (@lem1314067) (@lem1314066 x y x')). Qed.
Lemma lem1314069 (x : nadd) (x' : nadd) : (term312 x x') = (term312 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1314068 x y x')). Qed.
Lemma lem1314070 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314071 (x : nadd) (x' : nadd) : (term313 x x') = (term313 x x').
Proof. exact (MK_COMB (@lem1314070) (@lem1314069 x x')). Qed.
Lemma lem1314072 (x : nadd) : (term314 x) = (term314 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1314071 x x')). Qed.
Lemma lem1314073 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314074 (x : nadd) : (term315 x) = (term315 x).
Proof. exact (MK_COMB (@lem1314073) (@lem1314072 x)). Qed.
Lemma lem1314075 : term316 = term316.
Proof. exact (fun_ext (fun x : nadd => @lem1314074 x)). Qed.
Lemma lem1314076 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314078 : term317 = term317.
Proof. exact (MK_COMB (@lem1314076) (@lem1314075)). Qed.
Lemma lem1314079 (h1 : term299) : term317.
Proof. exact (EQ_MP (@lem1314078) (@lem1314026 h1)). Qed.
Lemma lem1314103 (y : nadd) (x : nadd) : (term80 y x) = (term80 y x).
Proof. exact (eq_refl (term80 y x)). Qed.
Lemma lem1314104 (x : nadd) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : nadd => @lem1314103 y x)). Qed.
Lemma lem1314105 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314106 (x : nadd) : (term92 x) = (term92 x).
Proof. exact (MK_COMB (@lem1314105) (@lem1314104 x)). Qed.
Lemma lem1314107 : term99 = term99.
Proof. exact (fun_ext (fun x : nadd => @lem1314106 x)). Qed.
Lemma lem1314108 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314110 : term114 = term114.
Proof. exact (MK_COMB (@lem1314108) (@lem1314107)). Qed.
Lemma lem1314111 (h1 : term61) : term114.
Proof. exact (EQ_MP (@lem1314110) (@lem1314027 h1)). Qed.
Lemma lem1314112 (_23380 : nadd) (h1 : term301) : term167 _23380.
Proof. exact (@lem1314051 h1 _23380). Qed.
Lemma lem1314113 (_23380 : nadd) : (term167 _23380) = (nadd_eq _23380 _23380).
Proof. exact (eq_refl (term167 _23380)). Qed.
Lemma lem1314115 (_23381 : nadd) (h1 : term299) : term326 _23381.
Proof. exact (@lem1314079 h1 _23381). Qed.
Lemma lem1314116 (_23381 : nadd) : (term326 _23381) = (term315 _23381).
Proof. exact (eq_refl (term326 _23381)). Qed.
Lemma lem1314117 (_23381 : nadd) (h1 : term299) : term315 _23381.
Proof. exact (EQ_MP (@lem1314116 _23381) (@lem1314115 _23381 h1)). Qed.
Lemma lem1314118 (_23381 : nadd) (_23382 : nadd) (h1 : term299) : term327 _23381 _23382.
Proof. exact (@lem1314117 _23381 h1 _23382). Qed.
Lemma lem1314119 (_23381 : nadd) (_23382 : nadd) : (term327 _23381 _23382) = (term313 _23381 _23382).
Proof. exact (eq_refl (term327 _23381 _23382)). Qed.
Lemma lem1314120 (_23381 : nadd) (_23382 : nadd) (h1 : term299) : term313 _23381 _23382.
Proof. exact (EQ_MP (@lem1314119 _23381 _23382) (@lem1314118 _23381 _23382 h1)). Qed.
Lemma lem1314121 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (h1 : term299) : term328 _23381 _23382 _23383.
Proof. exact (@lem1314120 _23381 _23382 h1 _23383). Qed.
Lemma lem1314122 (_23381 : nadd) (_23383 : nadd) (_23382 : nadd) : (term328 _23381 _23382 _23383) = (term311 _23381 _23383 _23382).
Proof. exact (eq_refl (term328 _23381 _23382 _23383)). Qed.
Lemma lem1314123 (_23381 : nadd) (_23383 : nadd) (_23382 : nadd) (h1 : term299) : term311 _23381 _23383 _23382.
Proof. exact (EQ_MP (@lem1314122 _23381 _23383 _23382) (@lem1314121 _23381 _23382 _23383 h1)). Qed.
Lemma lem1314124 (_23381 : nadd) (_23383 : nadd) (_23382 : nadd) (_23384 : nadd) (h1 : term299) : term329 _23381 _23383 _23382 _23384.
Proof. exact (@lem1314123 _23381 _23383 _23382 h1 _23384). Qed.
Lemma lem1314125 (_23381 : nadd) (_23383 : nadd) (_23382 : nadd) (_23384 : nadd) : (term329 _23381 _23383 _23382 _23384) = (term308 _23381 _23383 _23382 _23384).
Proof. exact (eq_refl (term329 _23381 _23383 _23382 _23384)). Qed.
Lemma lem1314126 (_23381 : nadd) (_23383 : nadd) (_23382 : nadd) (_23384 : nadd) (h1 : term299) : term308 _23381 _23383 _23382 _23384.
Proof. exact (EQ_MP (@lem1314125 _23381 _23383 _23382 _23384) (@lem1314124 _23381 _23383 _23382 _23384 h1)). Qed.
Lemma lem1314133 (_23387 : nadd) (h1 : term61) : term102 _23387.
Proof. exact (@lem1314111 h1 _23387). Qed.
Lemma lem1314134 (_23387 : nadd) : (term102 _23387) = (term92 _23387).
Proof. exact (eq_refl (term102 _23387)). Qed.
Lemma lem1314135 (_23387 : nadd) (h1 : term61) : term92 _23387.
Proof. exact (EQ_MP (@lem1314134 _23387) (@lem1314133 _23387 h1)). Qed.
Lemma lem1314136 (_23387 : nadd) (_23388 : nadd) (h1 : term61) : term79 _23387 _23388.
Proof. exact (@lem1314135 _23387 h1 _23388). Qed.
Lemma lem1314137 (_23388 : nadd) (_23387 : nadd) : (term79 _23387 _23388) = (term80 _23388 _23387).
Proof. exact (eq_refl (term79 _23387 _23388)). Qed.
Lemma lem1314140 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1314146 (y : nadd) (x : nadd) (h1 : term363 y x) : term363 y x.
Proof. exact (h1). Qed.
Lemma lem1314159 (_23381 : nadd) (_23383 : nadd) (_23382 : nadd) (_23384 : nadd) : (term308 _23381 _23383 _23382 _23384) = (term331 _23381 _23383 _23382 _23384).
Proof. exact (@lem1309080 (term132 _23381 _23382) (term132 _23383 _23384) (term304 _23381 _23383 _23382 _23384)). Qed.
Lemma lem1314160 (_23381 : nadd) (_23383 : nadd) (_23382 : nadd) (_23384 : nadd) (h1 : term299) : term331 _23381 _23383 _23382 _23384.
Proof. exact (EQ_MP (@lem1314159 _23381 _23383 _23382 _23384) (@lem1314126 _23381 _23383 _23382 _23384 h1)). Qed.
Lemma lem1314172 (_23388 : nadd) (_23387 : nadd) (h1 : term61) : term80 _23388 _23387.
Proof. exact (EQ_MP (@lem1314137 _23388 _23387) (@lem1314136 _23387 _23388 h1)). Qed.
Lemma lem1314174 (_23380 : nadd) (h1 : term301) : nadd_eq _23380 _23380.
Proof. exact (EQ_MP (@lem1314113 _23380) (@lem1314112 _23380 h1)). Qed.
Lemma lem1314175 (y : nadd) (h1 : term301) : term332 y.
Proof. exact (@lem1314174 (nadd_inv y) h1). Qed.
Lemma lem1314176 (y : nadd) (h1 : term301) : term333 y.
Proof. exact (fun h0 : term334 y => @lem1314175 y h1). Qed.
Lemma lem1314178 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1314179 (y : nadd) : (term333 y) = (term332 y).
Proof. exact (@lem1314178 (term332 y)). Qed.
Lemma lem1314180 (y : nadd) (h1 : term301) : term332 y.
Proof. exact (EQ_MP (@lem1314179 y) (@lem1314176 y h1)). Qed.
Lemma lem1314182 (_23380 : nadd) (h1 : term301) : nadd_eq _23380 _23380.
Proof. exact (EQ_MP (@lem1314113 _23380) (@lem1314112 _23380 h1)). Qed.
Lemma lem1314183 (x : nadd) (h1 : term301) : term332 x.
Proof. exact (@lem1314182 (nadd_inv x) h1). Qed.
Lemma lem1314184 (x : nadd) (h1 : term301) : term333 x.
Proof. exact (fun h0 : term334 x => @lem1314183 x h1). Qed.
Lemma lem1314186 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1314187 (x : nadd) : (term333 x) = (term332 x).
Proof. exact (@lem1314186 (term332 x)). Qed.
Lemma lem1314188 (x : nadd) (h1 : term301) : term332 x.
Proof. exact (EQ_MP (@lem1314187 x) (@lem1314184 x h1)). Qed.
Lemma lem1314190 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1314191 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term133 x y.
Proof. exact (fun h0 : term132 x y => @lem1314190 x y h1). Qed.
Lemma lem1314193 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1314194 (x : nadd) (y : nadd) : (term133 x y) = (nadd_eq x y).
Proof. exact (@lem1314193 (nadd_eq x y)). Qed.
Lemma lem1314195 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (EQ_MP (@lem1314194 x y) (@lem1314191 x y h1)). Qed.
Lemma lem1314211 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1314212 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : (term341 _23381 _23383 _23382 _23384) = (term342 _23381 _23382 _23383 _23384).
Proof. exact (@lem1314211 (term304 _23381 _23383 _23382 _23384) (term132 _23383 _23384)). Qed.
Lemma lem1314218 (_23381 : nadd) (_23382 : nadd) : (term146 _23381 _23382) = (term146 _23381 _23382).
Proof. exact (eq_refl (term146 _23381 _23382)). Qed.
Lemma lem1314219 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : (term331 _23381 _23383 _23382 _23384) = (term343 _23381 _23382 _23383 _23384).
Proof. exact (MK_COMB (@lem1314218 _23381 _23382) (@lem1314212 _23381 _23382 _23383 _23384)). Qed.
Lemma lem1314223 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1314224 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : (term343 _23381 _23382 _23383 _23384) = (term344 _23381 _23382 _23383 _23384).
Proof. exact (@lem1314223 (term304 _23381 _23383 _23382 _23384) (term132 _23381 _23382) (term132 _23383 _23384)). Qed.
Lemma lem1314240 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : (term331 _23381 _23383 _23382 _23384) = (term344 _23381 _23382 _23383 _23384).
Proof. exact (TRANS (@lem1314219 _23381 _23382 _23383 _23384) (@lem1314224 _23381 _23382 _23383 _23384)). Qed.
Lemma lem1314241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1314242 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : (term345 _23381 _23383 _23382 _23384) = (term346 _23381 _23382 _23383 _23384).
Proof. exact (MK_COMB (@lem1314241) (@lem1314240 _23381 _23382 _23383 _23384)). Qed.
Lemma lem1314258 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : (term344 _23381 _23382 _23383 _23384) = (term344 _23381 _23382 _23383 _23384).
Proof. exact (eq_refl (term344 _23381 _23382 _23383 _23384)). Qed.
Lemma lem1314259 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : ((term331 _23381 _23383 _23382 _23384) = (term344 _23381 _23382 _23383 _23384)) = ((term344 _23381 _23382 _23383 _23384) = (term344 _23381 _23382 _23383 _23384)).
Proof. exact (MK_COMB (@lem1314242 _23381 _23382 _23383 _23384) (@lem1314258 _23381 _23382 _23383 _23384)). Qed.
Lemma lem1314261 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1314262 (x : Prop) : (x = x) = True.
Proof. exact (@lem1314261 Prop x). Qed.
Lemma lem1314263 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : ((term344 _23381 _23382 _23383 _23384) = (term344 _23381 _23382 _23383 _23384)) = True.
Proof. exact (@lem1314262 (term344 _23381 _23382 _23383 _23384)). Qed.
Lemma lem1314264 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : ((term331 _23381 _23383 _23382 _23384) = (term344 _23381 _23382 _23383 _23384)) = True.
Proof. exact (TRANS (@lem1314259 _23381 _23382 _23383 _23384) (@lem1314263 _23381 _23382 _23383 _23384)). Qed.
Lemma lem1314265 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : True = ((term331 _23381 _23383 _23382 _23384) = (term344 _23381 _23382 _23383 _23384)).
Proof. exact (SYM (@lem1314264 _23381 _23382 _23383 _23384)). Qed.
Lemma lem1314266 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : (term331 _23381 _23383 _23382 _23384) = (term344 _23381 _23382 _23383 _23384).
Proof. exact (EQ_MP (@lem1314265 _23381 _23382 _23383 _23384) (@lem0)). Qed.
Lemma lem1314267 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) (h1 : term299) : term344 _23381 _23382 _23383 _23384.
Proof. exact (EQ_MP (@lem1314266 _23381 _23382 _23383 _23384) (@lem1314160 _23381 _23383 _23382 _23384 h1)). Qed.
Lemma lem1314269 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1314270 (_23381 : nadd) (_23383 : nadd) (_23382 : nadd) (_23384 : nadd) : (term344 _23381 _23382 _23383 _23384) = (term347 _23381 _23383 _23382 _23384).
Proof. exact (@lem1314269 (term303 _23381 _23382 _23383 _23384) (term304 _23381 _23383 _23382 _23384)). Qed.
Lemma lem1314272 (a : Prop) (b : Prop) : (term152 a b) = (term153 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1314273 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : (term348 _23381 _23382 _23383 _23384) = (term349 _23381 _23382 _23383 _23384).
Proof. exact (@lem1314272 (term132 _23381 _23382) (term132 _23383 _23384)). Qed.
Lemma lem1314275 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1314276 (_23381 : nadd) (_23382 : nadd) : (term140 _23381 _23382) = (nadd_eq _23381 _23382).
Proof. exact (@lem1314275 (nadd_eq _23381 _23382)). Qed.
Lemma lem1314277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1314278 (_23381 : nadd) (_23382 : nadd) : (term156 _23381 _23382) = (term157 _23381 _23382).
Proof. exact (MK_COMB (@lem1314277) (@lem1314276 _23381 _23382)). Qed.
Lemma lem1314280 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1314281 (_23383 : nadd) (_23384 : nadd) : (term140 _23383 _23384) = (nadd_eq _23383 _23384).
Proof. exact (@lem1314280 (nadd_eq _23383 _23384)). Qed.
Lemma lem1314282 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : (term349 _23381 _23382 _23383 _23384) = (term309 _23381 _23382 _23383 _23384).
Proof. exact (MK_COMB (@lem1314278 _23381 _23382) (@lem1314281 _23383 _23384)). Qed.
Lemma lem1314283 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : (term348 _23381 _23382 _23383 _23384) = (term309 _23381 _23382 _23383 _23384).
Proof. exact (TRANS (@lem1314273 _23381 _23382 _23383 _23384) (@lem1314282 _23381 _23382 _23383 _23384)). Qed.
Lemma lem1314284 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1314285 (_23381 : nadd) (_23382 : nadd) (_23383 : nadd) (_23384 : nadd) : (term350 _23381 _23382 _23383 _23384) = (term351 _23381 _23382 _23383 _23384).
Proof. exact (MK_COMB (@lem1314284) (@lem1314283 _23381 _23382 _23383 _23384)). Qed.
Lemma lem1314286 (_23381 : nadd) (_23383 : nadd) (_23382 : nadd) (_23384 : nadd) : (term304 _23381 _23383 _23382 _23384) = (term304 _23381 _23383 _23382 _23384).
Proof. exact (eq_refl (term304 _23381 _23383 _23382 _23384)). Qed.
Lemma lem1314287 (_23381 : nadd) (_23383 : nadd) (_23382 : nadd) (_23384 : nadd) : (term347 _23381 _23383 _23382 _23384) = (term291 _23381 _23383 _23382 _23384).
Proof. exact (MK_COMB (@lem1314285 _23381 _23382 _23383 _23384) (@lem1314286 _23381 _23383 _23382 _23384)). Qed.
Lemma lem1314288 (_23381 : nadd) (_23383 : nadd) (_23382 : nadd) (_23384 : nadd) : (term344 _23381 _23382 _23383 _23384) = (term291 _23381 _23383 _23382 _23384).
Proof. exact (TRANS (@lem1314270 _23381 _23383 _23382 _23384) (@lem1314287 _23381 _23383 _23382 _23384)). Qed.
Lemma lem1314290 (x : nadd) (y : nadd) (h1 : term301) (h2 : nadd_eq x y) : term390 x y.
Proof. exact (conj (@lem1314188 x h1) (@lem1314195 x y h2)). Qed.
Lemma lem1314292 (_23381 : nadd) (_23383 : nadd) (_23382 : nadd) (_23384 : nadd) (h1 : term299) : term291 _23381 _23383 _23382 _23384.
Proof. exact (EQ_MP (@lem1314288 _23381 _23383 _23382 _23384) (@lem1314267 _23381 _23382 _23383 _23384 h1)). Qed.
Lemma lem1314293 (x : nadd) (y : nadd) (h1 : term299) : term391 x y.
Proof. exact (@lem1314292 (nadd_inv x) x (nadd_inv x) y h1). Qed.
Lemma lem1314296 (x : nadd) (y : nadd) (h1 : term299) (h2 : term301) (h3 : nadd_eq x y) : term392 x y.
Proof. exact (@lem1314293 x y h1 (@lem1314290 x y h2 h3)). Qed.
Lemma lem1314297 (x : nadd) (y : nadd) (h1 : term299) (h2 : term301) (h3 : nadd_eq x y) : term393 x y.
Proof. exact (fun h0 : term394 x y => @lem1314296 x y h1 h2 h3). Qed.
Lemma lem1314299 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1314300 (x : nadd) (y : nadd) : (term393 x y) = (term392 x y).
Proof. exact (@lem1314299 (term392 x y)). Qed.
Lemma lem1314301 (x : nadd) (y : nadd) (h1 : term299) (h2 : term301) (h3 : nadd_eq x y) : term392 x y.
Proof. exact (EQ_MP (@lem1314300 x y) (@lem1314297 x y h1 h2 h3)). Qed.
Lemma lem1314302 (x : nadd) (y : nadd) (h1 : term299) (h2 : term301) (h3 : nadd_eq x y) : term395 x y.
Proof. exact (conj (@lem1314180 y h2) (@lem1314301 x y h1 h2 h3)). Qed.
Lemma lem1314304 (_23381 : nadd) (_23383 : nadd) (_23382 : nadd) (_23384 : nadd) (h1 : term299) : term291 _23381 _23383 _23382 _23384.
Proof. exact (EQ_MP (@lem1314288 _23381 _23383 _23382 _23384) (@lem1314267 _23381 _23382 _23383 _23384 h1)). Qed.
Lemma lem1314305 (x : nadd) (y : nadd) (h1 : term299) : term396 x y.
Proof. exact (@lem1314304 (nadd_inv y) (term354 x) (nadd_inv y) (term397 x y) h1). Qed.
Lemma lem1314308 (x : nadd) (y : nadd) (h1 : term299) (h2 : term301) (h3 : nadd_eq x y) : term398 x y.
Proof. exact (@lem1314305 x y h1 (@lem1314302 x y h1 h2 h3)). Qed.
Lemma lem1314309 (x : nadd) (y : nadd) (h1 : term299) (h2 : term301) (h3 : nadd_eq x y) : term399 x y.
Proof. exact (fun h0 : term400 x y => @lem1314308 x y h1 h2 h3). Qed.
Lemma lem1314311 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1314312 (x : nadd) (y : nadd) : (term399 x y) = (term398 x y).
Proof. exact (@lem1314311 (term398 x y)). Qed.
Lemma lem1314313 (x : nadd) (y : nadd) (h1 : term299) (h2 : term301) (h3 : nadd_eq x y) : term398 x y.
Proof. exact (EQ_MP (@lem1314312 x y) (@lem1314309 x y h1 h2 h3)). Qed.
Lemma lem1314319 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1314320 (_23387 : nadd) (_23388 : nadd) : (term80 _23388 _23387) = (term76 _23387 _23388).
Proof. exact (@lem1314319 (nadd_eq _23388 _23387) (term132 _23387 _23388)). Qed.
Lemma lem1314326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1314327 (_23387 : nadd) (_23388 : nadd) : (term135 _23388 _23387) = (term136 _23387 _23388).
Proof. exact (MK_COMB (@lem1314326) (@lem1314320 _23387 _23388)). Qed.
Lemma lem1314333 (_23387 : nadd) (_23388 : nadd) : (term76 _23387 _23388) = (term76 _23387 _23388).
Proof. exact (eq_refl (term76 _23387 _23388)). Qed.
Lemma lem1314334 (_23387 : nadd) (_23388 : nadd) : ((term80 _23388 _23387) = (term76 _23387 _23388)) = ((term76 _23387 _23388) = (term76 _23387 _23388)).
Proof. exact (MK_COMB (@lem1314327 _23387 _23388) (@lem1314333 _23387 _23388)). Qed.
Lemma lem1314336 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1314337 (x : Prop) : (x = x) = True.
Proof. exact (@lem1314336 Prop x). Qed.
Lemma lem1314338 (_23387 : nadd) (_23388 : nadd) : ((term76 _23387 _23388) = (term76 _23387 _23388)) = True.
Proof. exact (@lem1314337 (term76 _23387 _23388)). Qed.
Lemma lem1314339 (_23387 : nadd) (_23388 : nadd) : ((term80 _23388 _23387) = (term76 _23387 _23388)) = True.
Proof. exact (TRANS (@lem1314334 _23387 _23388) (@lem1314338 _23387 _23388)). Qed.
Lemma lem1314340 (_23387 : nadd) (_23388 : nadd) : True = ((term80 _23388 _23387) = (term76 _23387 _23388)).
Proof. exact (SYM (@lem1314339 _23387 _23388)). Qed.
Lemma lem1314341 (_23387 : nadd) (_23388 : nadd) : (term80 _23388 _23387) = (term76 _23387 _23388).
Proof. exact (EQ_MP (@lem1314340 _23387 _23388) (@lem0)). Qed.
Lemma lem1314342 (_23387 : nadd) (_23388 : nadd) (h1 : term61) : term76 _23387 _23388.
Proof. exact (EQ_MP (@lem1314341 _23387 _23388) (@lem1314172 _23388 _23387 h1)). Qed.
Lemma lem1314344 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1314345 (_23388 : nadd) (_23387 : nadd) : (term76 _23387 _23388) = (term138 _23388 _23387).
Proof. exact (@lem1314344 (term132 _23387 _23388) (nadd_eq _23388 _23387)). Qed.
Lemma lem1314347 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1314348 (_23387 : nadd) (_23388 : nadd) : (term140 _23387 _23388) = (nadd_eq _23387 _23388).
Proof. exact (@lem1314347 (nadd_eq _23387 _23388)). Qed.
Lemma lem1314349 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1314350 (_23387 : nadd) (_23388 : nadd) : (term141 _23387 _23388) = (term45 _23387 _23388).
Proof. exact (MK_COMB (@lem1314349) (@lem1314348 _23387 _23388)). Qed.
Lemma lem1314351 (_23388 : nadd) (_23387 : nadd) : (nadd_eq _23388 _23387) = (nadd_eq _23388 _23387).
Proof. exact (eq_refl (nadd_eq _23388 _23387)). Qed.
Lemma lem1314352 (_23388 : nadd) (_23387 : nadd) : (term138 _23388 _23387) = (term142 _23388 _23387).
Proof. exact (MK_COMB (@lem1314350 _23387 _23388) (@lem1314351 _23388 _23387)). Qed.
Lemma lem1314353 (_23388 : nadd) (_23387 : nadd) : (term76 _23387 _23388) = (term142 _23388 _23387).
Proof. exact (TRANS (@lem1314345 _23388 _23387) (@lem1314352 _23388 _23387)). Qed.
Lemma lem1314356 (_23388 : nadd) (_23387 : nadd) (h1 : term61) : term142 _23388 _23387.
Proof. exact (EQ_MP (@lem1314353 _23388 _23387) (@lem1314342 _23387 _23388 h1)). Qed.
Lemma lem1314357 (y : nadd) (x : nadd) (h1 : term61) : term401 y x.
Proof. exact (@lem1314356 (term402 x y) (term360 y x) h1). Qed.
Lemma lem1314360 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : nadd_eq x y) : term361 y x.
Proof. exact (@lem1314357 y x h2 (@lem1314313 x y h1 h3 h4)). Qed.
Lemma lem1314361 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : nadd_eq x y) : term403 y x.
Proof. exact (fun h0 : term363 y x => @lem1314360 x y h1 h2 h3 h4). Qed.
Lemma lem1314363 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1314364 (y : nadd) (x : nadd) : (term403 y x) = (term361 y x).
Proof. exact (@lem1314363 (term361 y x)). Qed.
Lemma lem1314365 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : nadd_eq x y) : term361 y x.
Proof. exact (EQ_MP (@lem1314364 y x) (@lem1314361 x y h1 h2 h3 h4)). Qed.
Lemma lem1314368 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1314370 (y : nadd) (x : nadd) : (term363 y x) = (term404 y x).
Proof. exact (@lem1314368 (term361 y x)). Qed.
Lemma lem1314373 (y : nadd) (x : nadd) (h1 : term363 y x) : term404 y x.
Proof. exact (EQ_MP (@lem1314370 y x) (@lem1314146 y x h1)). Qed.
Lemma lem1314376 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (@lem1314373 y x h4 (@lem1314365 x y h1 h2 h3 h5)). Qed.
Lemma lem1314377 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : term164.
Proof. exact (fun h0 : ~ False => @lem1314376 x y h1 h2 h3 h4 h5). Qed.
Lemma lem1314379 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1314380 : term164 = False.
Proof. exact (@lem1314379 False). Qed.
Lemma lem1314381 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314380) (@lem1314377 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1314382 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : (term363 y x) = False.
Proof. exact (prop_ext (fun h6 : term363 y x => @lem1314381 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1314146 y x h4)). Qed.
Lemma lem1314383 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314382 x y h1 h2 h3 h4 h5) (@lem1314146 y x h4)). Qed.
Lemma lem1314384 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h6 : nadd_eq x y => @lem1314383 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1314140 x y h5)). Qed.
Lemma lem1314385 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314384 x y h1 h2 h3 h4 h5) (@lem1314140 x y h5)). Qed.
Lemma lem1314386 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : (term363 y x) = False.
Proof. exact (prop_ext (fun h6 : term363 y x => @lem1314385 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1314044 y x h4)). Qed.
Lemma lem1314387 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314386 x y h1 h2 h3 h4 h5) (@lem1314044 y x h4)). Qed.
Lemma lem1314388 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h6 : nadd_eq x y => @lem1314387 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1314032 x y h5)). Qed.
Lemma lem1314389 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314388 x y h1 h2 h3 h4 h5) (@lem1314032 x y h5)). Qed.
Lemma lem1314390 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : term301 = False.
Proof. exact (prop_ext (fun h6 : term301 => @lem1314389 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1314051 h3)). Qed.
Lemma lem1314391 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314390 x y h1 h2 h3 h4 h5) (@lem1314051 h3)). Qed.
Lemma lem1314392 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : (term363 y x) = False.
Proof. exact (prop_ext (fun h6 : term363 y x => @lem1314391 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1314044 y x h4)). Qed.
Lemma lem1314393 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314392 x y h1 h2 h3 h4 h5) (@lem1314044 y x h4)). Qed.
Lemma lem1314394 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h6 : nadd_eq x y => @lem1314393 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1314032 x y h5)). Qed.
Lemma lem1314395 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314394 x y h1 h2 h3 h4 h5) (@lem1314032 x y h5)). Qed.
Lemma lem1314396 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : term301 = False.
Proof. exact (prop_ext (fun h6 : term301 => @lem1314395 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1313980 h3)). Qed.
Lemma lem1314397 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314396 x y h1 h2 h3 h4 h5) (@lem1313980 h3)). Qed.
Lemma lem1314398 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : (term363 y x) = False.
Proof. exact (prop_ext (fun h6 : term363 y x => @lem1314397 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1313925 y x h4)). Qed.
Lemma lem1314399 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314398 x y h1 h2 h3 h4 h5) (@lem1313925 y x h4)). Qed.
Lemma lem1314400 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h6 : nadd_eq x y => @lem1314399 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1313869 x y h5)). Qed.
Lemma lem1314401 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314400 x y h1 h2 h3 h4 h5) (@lem1313869 x y h5)). Qed.
Lemma lem1314402 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : term301 = False.
Proof. exact (prop_ext (fun h6 : term301 => @lem1314401 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1313773 h3)). Qed.
Lemma lem1314403 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314402 x y h1 h2 h3 h4 h5) (@lem1313773 h3)). Qed.
Lemma lem1314404 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : (term363 y x) = False.
Proof. exact (prop_ext (fun h6 : term363 y x => @lem1314403 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1313473 y x h4)). Qed.
Lemma lem1314405 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314404 x y h1 h2 h3 h4 h5) (@lem1313473 y x h4)). Qed.
Lemma lem1314406 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : (nadd_eq x y) = False.
Proof. exact (prop_ext (fun h6 : nadd_eq x y => @lem1314405 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1313455 x y h5)). Qed.
Lemma lem1314407 (x : nadd) (y : nadd) (h1 : term299) (h2 : term61) (h3 : term301) (h4 : term363 y x) (h5 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314406 x y h1 h2 h3 h4 h5) (@lem1313455 x y h5)). Qed.
Lemma lem1314408 (x : nadd) (y : nadd) (h1 : term61) (h2 : term301) (h3 : term363 y x) (h4 : nadd_eq x y) : term368.
Proof. exact (fun h0 : term299 => @lem1314407 x y h0 h1 h2 h3 h4). Qed.
Lemma lem1314409 : term368 = term369.
Proof. exact (@lem69 term299). Qed.
Lemma lem1314410 (x : nadd) (y : nadd) (h1 : term61) (h2 : term301) (h3 : term363 y x) (h4 : nadd_eq x y) : term369.
Proof. exact (EQ_MP (@lem1314409) (@lem1314408 x y h1 h2 h3 h4)). Qed.
Lemma lem1314411 (x : nadd) (y : nadd) (h1 : term61) (h2 : term363 y x) (h3 : nadd_eq x y) : term371.
Proof. exact (fun h0 : term301 => @lem1314410 x y h1 h0 h2 h3). Qed.
Lemma lem1314412 (x : nadd) (y : nadd) (h1 : term363 y x) (h2 : nadd_eq x y) : term373.
Proof. exact (fun h0 : term61 => @lem1314411 x y h0 h1 h2). Qed.
Lemma lem1314413 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term376 y x.
Proof. exact (fun h0 : term363 y x => @lem1314412 x y h0 h1). Qed.
Lemma lem1314414 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term378 y x.
Proof. exact (fun h0 : term27 y => @lem1314413 x y h1). Qed.
Lemma lem1314415 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term380 y x.
Proof. exact (fun h0 : term27 x => @lem1314414 x y h1). Qed.
Lemma lem1314416 (y : nadd) (x : nadd) : term381 y x.
Proof. exact (fun h0 : nadd_eq x y => @lem1314415 x y h0). Qed.
Lemma lem1314421 (x : nadd) : term385 x.
Proof. exact (fun y : nadd => @lem1314416 y x). Qed.
Lemma lem1314426 : term389.
Proof. exact (fun x : nadd => @lem1314421 x). Qed.
Lemma lem1314427 : term388.
Proof. exact (EQ_MP (@lem1313442) (@lem1314426)). Qed.
Lemma lem1314428 (x : nadd) : term405 x.
Proof. exact (@lem1314427 x). Qed.
Lemma lem1314429 (x : nadd) : (term405 x) = (term384 x).
Proof. exact (eq_refl (term405 x)). Qed.
Lemma lem1314430 (x : nadd) : term384 x.
Proof. exact (EQ_MP (@lem1314429 x) (@lem1314428 x)). Qed.
Lemma lem1314431 (x : nadd) (y : nadd) : term406 x y.
Proof. exact (@lem1314430 x y). Qed.
Lemma lem1314432 (y : nadd) (x : nadd) : (term406 x y) = (term364 y x).
Proof. exact (eq_refl (term406 x y)). Qed.
Lemma lem1314433 (y : nadd) (x : nadd) : term364 y x.
Proof. exact (EQ_MP (@lem1314432 y x) (@lem1314431 x y)). Qed.
Lemma lem1314435 (y : nadd) (x : nadd) : term364 y x.
Proof. exact (@lem1313199 y x (@lem1314433 y x)). Qed.
Lemma lem1314436 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term379 y x.
Proof. exact (@lem1314435 y x (@lem1309210 x y h1)). Qed.
Lemma lem1314437 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) : term377 y x.
Proof. exact (@lem1314436 x y h2 (@lem1309209 x h1)). Qed.
Lemma lem1314438 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term375 y x.
Proof. exact (@lem1314437 x y h1 h3 (@lem1310360 y h2)). Qed.
Lemma lem1314439 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term363 y x) (h4 : nadd_eq x y) : term372.
Proof. exact (@lem1314438 x y h1 h2 h4 (@lem1313184 y x h3)). Qed.
Lemma lem1314440 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term363 y x) (h4 : nadd_eq x y) : term370.
Proof. exact (@lem1314439 x y h1 h2 h3 h4 (@lem1268060)). Qed.
Lemma lem1314441 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term363 y x) (h4 : nadd_eq x y) : term368.
Proof. exact (@lem1314440 x y h1 h2 h3 h4 (@lem1267990)). Qed.
Lemma lem1314442 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term363 y x) (h4 : nadd_eq x y) : False.
Proof. exact (@lem1314441 x y h1 h2 h3 h4 (@lem1279298)). Qed.
Lemma lem1314443 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term363 y x) (h4 : nadd_eq x y) : (term363 y x) = False.
Proof. exact (prop_ext (fun h5 : term363 y x => @lem1314442 x y h1 h2 h3 h4) (fun h5 : False => @lem1313184 y x h3)). Qed.
Lemma lem1314444 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term363 y x) (h4 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1314443 x y h1 h2 h3 h4) (@lem1313184 y x h3)). Qed.
Lemma lem1314445 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term362 y x.
Proof. exact (fun h0 : term363 y x => @lem1314444 x y h1 h2 h0 h3). Qed.
Lemma lem1314446 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term361 y x.
Proof. exact (EQ_MP (@lem1313183 y x) (@lem1314445 x y h1 h2 h3)). Qed.
Lemma lem1314448 (x : nadd) (z : nadd) : term18 x z.
Proof. exact (EQ_MP (@lem1309069 x z) (@lem1309068 x z)). Qed.
Lemma lem1314449 (x : nadd) (y : nadd) : term407 x y.
Proof. exact (@lem1314448 (nadd_inv x) (term402 x y)). Qed.
Lemma lem1314451 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1314452 (x : nadd) (y : nadd) : (term408 x y) = (term409 x y).
Proof. exact (@lem1314451 (term408 x y)). Qed.
Lemma lem1314453 (x : nadd) (y : nadd) : (term409 x y) = (term408 x y).
Proof. exact (SYM (@lem1314452 x y)). Qed.
Lemma lem1314454 (x : nadd) (y : nadd) (h1 : term410 x y) : term410 x y.
Proof. exact (h1). Qed.
Lemma lem1314457 (x : nadd) (y : nadd) (h1 : term411 x y) : term411 x y.
Proof. exact (h1). Qed.
Lemma lem1314458 (x : nadd) (y : nadd) : term412 x y.
Proof. exact (fun h0 : term411 x y => @lem1314457 x y h0). Qed.
Lemma lem1314459 (x : nadd) (y : nadd) (h1 : term412 x y) : term412 x y.
Proof. exact (h1). Qed.
Lemma lem1314460 (x : nadd) (y : nadd) (h1 : term411 x y) : term411 x y.
Proof. exact (h1). Qed.
Lemma lem1314461 (x : nadd) (y : nadd) (h1 : term412 x y) (h2 : term411 x y) : term411 x y.
Proof. exact (@lem1314459 x y h1 (@lem1314460 x y h2)). Qed.
Lemma lem1314462 (x : nadd) (y : nadd) (h1 : term411 x y) : term413 x y.
Proof. exact (fun h0 : term412 x y => @lem1314461 x y h0 h1). Qed.
Lemma lem1314463 (x : nadd) (y : nadd) (h1 : term412 x y) : term412 x y.
Proof. exact (h1). Qed.
Lemma lem1314464 (x : nadd) (y : nadd) (h1 : term412 x y) (h2 : term411 x y) : term411 x y.
Proof. exact (@lem1314462 x y h2 (@lem1314463 x y h1)). Qed.
Lemma lem1314465 (x : nadd) (y : nadd) (h1 : term412 x y) : term412 x y.
Proof. exact (fun h0 : term411 x y => @lem1314464 x y h1 h0). Qed.
Lemma lem1314466 (x : nadd) (y : nadd) : term414 x y.
Proof. exact (fun h0 : term412 x y => @lem1314465 x y h0). Qed.
Lemma lem1314469 (x : nadd) (y : nadd) : term412 x y.
Proof. exact (@lem1314466 x y (@lem1314458 x y)). Qed.
Lemma lem1314543 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1314544 : term415 = term416.
Proof. exact (@lem1314543 term417). Qed.
Lemma lem1314557 : term418 = term418.
Proof. exact (eq_refl term418). Qed.
Lemma lem1314558 : term419 = term420.
Proof. exact (MK_COMB (@lem1314557) (@lem1314544)). Qed.
Lemma lem1314561 : term212 = term212.
Proof. exact (eq_refl term212). Qed.
Lemma lem1314562 : term421 = term422.
Proof. exact (MK_COMB (@lem1314561) (@lem1314558)). Qed.
Lemma lem1314565 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem1314566 : term423 = term424.
Proof. exact (MK_COMB (@lem1314565) (@lem1314562)). Qed.
Lemma lem1314569 : term270 = term270.
Proof. exact (eq_refl term270). Qed.
Lemma lem1314570 : term425 = term426.
Proof. exact (MK_COMB (@lem1314569) (@lem1314566)). Qed.
Lemma lem1314573 (x : nadd) (y : nadd) : (term427 x y) = (term427 x y).
Proof. exact (eq_refl (term427 x y)). Qed.
Lemma lem1314574 (x : nadd) (y : nadd) : (term428 x y) = (term429 x y).
Proof. exact (MK_COMB (@lem1314573 x y) (@lem1314570)). Qed.
Lemma lem1314577 (y : nadd) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem1314578 (x : nadd) (y : nadd) : (term430 x y) = (term431 x y).
Proof. exact (MK_COMB (@lem1314577 y) (@lem1314574 x y)). Qed.
Lemma lem1314581 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1314582 (x : nadd) (y : nadd) : (term432 x y) = (term433 x y).
Proof. exact (MK_COMB (@lem1314581 x) (@lem1314578 x y)). Qed.
Lemma lem1314585 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1314586 (x : nadd) (y : nadd) : (term411 x y) = (term434 x y).
Proof. exact (MK_COMB (@lem1314585 x y) (@lem1314582 x y)). Qed.
Lemma lem1314589 (y : nadd) : (term435 y) = (term436 y).
Proof. exact (fun_ext (fun x : nadd => @lem1314586 x y)). Qed.
Lemma lem1314590 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314591 (y : nadd) : (term437 y) = (term438 y).
Proof. exact (MK_COMB (@lem1314590) (@lem1314589 y)). Qed.
Lemma lem1314596 : term439 = term440.
Proof. exact (fun_ext (fun y : nadd => @lem1314591 y)). Qed.
Lemma lem1314597 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314606 : term441 = term442.
Proof. exact (MK_COMB (@lem1314597) (@lem1314596)). Qed.
Lemma lem1314607 (x : nadd) (y : nadd) (z : nadd) : (term443 x y z) = (term443 x y z).
Proof. exact (eq_refl (term443 x y z)). Qed.
Lemma lem1314608 (x : nadd) (y : nadd) : (term444 x y) = (term444 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1314607 x y z)). Qed.
Lemma lem1314609 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314610 (x : nadd) (y : nadd) : (term445 x y) = (term445 x y).
Proof. exact (MK_COMB (@lem1314609) (@lem1314608 x y)). Qed.
Lemma lem1314611 (x : nadd) : (term446 x) = (term446 x).
Proof. exact (fun_ext (fun y : nadd => @lem1314610 x y)). Qed.
Lemma lem1314612 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314613 (x : nadd) : (term447 x) = (term447 x).
Proof. exact (MK_COMB (@lem1314612) (@lem1314611 x)). Qed.
Lemma lem1314614 : term448 = term448.
Proof. exact (fun_ext (fun x : nadd => @lem1314613 x)). Qed.
Lemma lem1314615 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314616 : term417 = term417.
Proof. exact (MK_COMB (@lem1314615) (@lem1314614)). Qed.
Lemma lem1314617 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1314618 : term416 = term416.
Proof. exact (MK_COMB (@lem1314617) (@lem1314616)). Qed.
Lemma lem1314619 (y : nadd) (x : nadd) : (term231 y x) = (term231 y x).
Proof. exact (eq_refl (term231 y x)). Qed.
Lemma lem1314620 (x : nadd) : (term232 x) = (term232 x).
Proof. exact (fun_ext (fun y : nadd => @lem1314619 y x)). Qed.
Lemma lem1314621 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314622 (x : nadd) : (term233 x) = (term233 x).
Proof. exact (MK_COMB (@lem1314621) (@lem1314620 x)). Qed.
Lemma lem1314623 : term234 = term234.
Proof. exact (fun_ext (fun x : nadd => @lem1314622 x)). Qed.
Lemma lem1314624 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314625 : term208 = term208.
Proof. exact (MK_COMB (@lem1314624) (@lem1314623)). Qed.
Lemma lem1314626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1314627 : term418 = term418.
Proof. exact (MK_COMB (@lem1314626) (@lem1314625)). Qed.
Lemma lem1314628 : term420 = term420.
Proof. exact (MK_COMB (@lem1314627) (@lem1314618)). Qed.
Lemma lem1314637 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term13 y x z).
Proof. exact (eq_refl (term13 y x z)). Qed.
Lemma lem1314638 (y : nadd) (x : nadd) : (term55 y x) = (term55 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1314637 y x z)). Qed.
Lemma lem1314639 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314640 (y : nadd) (x : nadd) : (term11 y x) = (term11 y x).
Proof. exact (MK_COMB (@lem1314639) (@lem1314638 y x)). Qed.
Lemma lem1314641 (x : nadd) : (term56 x) = (term56 x).
Proof. exact (fun_ext (fun y : nadd => @lem1314640 y x)). Qed.
Lemma lem1314642 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314643 (x : nadd) : (term9 x) = (term9 x).
Proof. exact (MK_COMB (@lem1314642) (@lem1314641 x)). Qed.
Lemma lem1314644 : term57 = term57.
Proof. exact (fun_ext (fun x : nadd => @lem1314643 x)). Qed.
Lemma lem1314645 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314646 : term7 = term7.
Proof. exact (MK_COMB (@lem1314645) (@lem1314644)). Qed.
Lemma lem1314647 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1314648 : term212 = term212.
Proof. exact (MK_COMB (@lem1314647) (@lem1314646)). Qed.
Lemma lem1314649 : term422 = term422.
Proof. exact (MK_COMB (@lem1314648) (@lem1314628)). Qed.
Lemma lem1314658 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term291 x y x' y') = (term291 x y x' y').
Proof. exact (eq_refl (term291 x y x' y')). Qed.
Lemma lem1314659 (x : nadd) (y : nadd) (x' : nadd) : (term292 x y x') = (term292 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1314658 x y x' y')). Qed.
Lemma lem1314660 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314661 (x : nadd) (y : nadd) (x' : nadd) : (term293 x y x') = (term293 x y x').
Proof. exact (MK_COMB (@lem1314660) (@lem1314659 x y x')). Qed.
Lemma lem1314662 (x : nadd) (x' : nadd) : (term294 x x') = (term294 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1314661 x y x')). Qed.
Lemma lem1314663 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314664 (x : nadd) (x' : nadd) : (term295 x x') = (term295 x x').
Proof. exact (MK_COMB (@lem1314663) (@lem1314662 x x')). Qed.
Lemma lem1314665 (x : nadd) : (term296 x) = (term296 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1314664 x x')). Qed.
Lemma lem1314666 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314667 (x : nadd) : (term297 x) = (term297 x).
Proof. exact (MK_COMB (@lem1314666) (@lem1314665 x)). Qed.
Lemma lem1314668 : term298 = term298.
Proof. exact (fun_ext (fun x : nadd => @lem1314667 x)). Qed.
Lemma lem1314669 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314670 : term299 = term299.
Proof. exact (MK_COMB (@lem1314669) (@lem1314668)). Qed.
Lemma lem1314671 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1314672 : term267 = term267.
Proof. exact (MK_COMB (@lem1314671) (@lem1314670)). Qed.
Lemma lem1314673 : term424 = term424.
Proof. exact (MK_COMB (@lem1314672) (@lem1314649)). Qed.
Lemma lem1314674 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1314675 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1314674 x)). Qed.
Lemma lem1314676 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314677 : term301 = term301.
Proof. exact (MK_COMB (@lem1314676) (@lem1314675)). Qed.
Lemma lem1314678 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1314679 : term270 = term270.
Proof. exact (MK_COMB (@lem1314678) (@lem1314677)). Qed.
Lemma lem1314680 : term426 = term426.
Proof. exact (MK_COMB (@lem1314679) (@lem1314673)). Qed.
Lemma lem1314685 (x : nadd) (y : nadd) : (term427 x y) = (term427 x y).
Proof. exact (eq_refl (term427 x y)). Qed.
Lemma lem1314686 (x : nadd) (y : nadd) : (term429 x y) = (term429 x y).
Proof. exact (MK_COMB (@lem1314685 x y) (@lem1314680)). Qed.
Lemma lem1314691 (y : nadd) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem1314692 (x : nadd) (y : nadd) : (term431 x y) = (term431 x y).
Proof. exact (MK_COMB (@lem1314691 y) (@lem1314686 x y)). Qed.
Lemma lem1314697 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1314698 (x : nadd) (y : nadd) : (term433 x y) = (term433 x y).
Proof. exact (MK_COMB (@lem1314697 x) (@lem1314692 x y)). Qed.
Lemma lem1314701 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1314702 (x : nadd) (y : nadd) : (term434 x y) = (term434 x y).
Proof. exact (MK_COMB (@lem1314701 x y) (@lem1314698 x y)). Qed.
Lemma lem1314703 (y : nadd) : (term436 y) = (term436 y).
Proof. exact (fun_ext (fun x : nadd => @lem1314702 x y)). Qed.
Lemma lem1314704 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314705 (y : nadd) : (term438 y) = (term438 y).
Proof. exact (MK_COMB (@lem1314704) (@lem1314703 y)). Qed.
Lemma lem1314706 : term440 = term440.
Proof. exact (fun_ext (fun y : nadd => @lem1314705 y)). Qed.
Lemma lem1314707 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314708 : term442 = term442.
Proof. exact (MK_COMB (@lem1314707) (@lem1314706)). Qed.
Lemma lem1314825 : term441 = term442.
Proof. exact (TRANS (@lem1314606) (@lem1314708)). Qed.
Lemma lem1314826 : term442 = term441.
Proof. exact (SYM (@lem1314825)). Qed.
Lemma lem1314831 (h1 : term301) : term301.
Proof. exact (h1). Qed.
Lemma lem1314832 (h1 : term299) : term299.
Proof. exact (h1). Qed.
Lemma lem1314833 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1314834 (h1 : term208) : term208.
Proof. exact (h1). Qed.
Lemma lem1314835 (h1 : term417) : term417.
Proof. exact (h1). Qed.
Lemma lem1314859 (x : nadd) (y : nadd) (h1 : term410 x y) : term410 x y.
Proof. exact (h1). Qed.
Lemma lem1314860 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1314861 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1314860 x)). Qed.
Lemma lem1314862 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314871 : term301 = term301.
Proof. exact (MK_COMB (@lem1314862) (@lem1314861)). Qed.
Lemma lem1314872 (h1 : term301) : term301.
Proof. exact (EQ_MP (@lem1314871) (@lem1314831 h1)). Qed.
Lemma lem1314879 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term302 x x' y y') = (term303 x x' y y').
Proof. exact (@lem17045 (nadd_eq x x') (nadd_eq y y')). Qed.
Lemma lem1314880 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term304 x y x' y') = (term304 x y x' y').
Proof. exact (eq_refl (term304 x y x' y')). Qed.
Lemma lem1314881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1314882 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term305 x x' y y') = (term306 x x' y y').
Proof. exact (MK_COMB (@lem1314881) (@lem1314879 x x' y y')). Qed.
Lemma lem1314883 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term307 x y x' y') = (term308 x y x' y').
Proof. exact (MK_COMB (@lem1314882 x x' y y') (@lem1314880 x y x' y')). Qed.
Lemma lem1314884 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term291 x y x' y') = (term307 x y x' y').
Proof. exact (@lem17265 (term309 x x' y y') (term304 x y x' y')). Qed.
Lemma lem1314885 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term291 x y x' y') = (term308 x y x' y').
Proof. exact (TRANS (@lem1314884 x y x' y') (@lem1314883 x y x' y')). Qed.
Lemma lem1314886 (x : nadd) (y : nadd) (x' : nadd) : (term292 x y x') = (term310 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1314885 x y x' y')). Qed.
Lemma lem1314887 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314888 (x : nadd) (y : nadd) (x' : nadd) : (term293 x y x') = (term311 x y x').
Proof. exact (MK_COMB (@lem1314887) (@lem1314886 x y x')). Qed.
Lemma lem1314889 (x : nadd) (x' : nadd) : (term294 x x') = (term312 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1314888 x y x')). Qed.
Lemma lem1314890 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314891 (x : nadd) (x' : nadd) : (term295 x x') = (term313 x x').
Proof. exact (MK_COMB (@lem1314890) (@lem1314889 x x')). Qed.
Lemma lem1314892 (x : nadd) : (term296 x) = (term314 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1314891 x x')). Qed.
Lemma lem1314893 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314894 (x : nadd) : (term297 x) = (term315 x).
Proof. exact (MK_COMB (@lem1314893) (@lem1314892 x)). Qed.
Lemma lem1314895 : term298 = term316.
Proof. exact (fun_ext (fun x : nadd => @lem1314894 x)). Qed.
Lemma lem1314896 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314961 : term299 = term317.
Proof. exact (MK_COMB (@lem1314896) (@lem1314895)). Qed.
Lemma lem1314962 (h1 : term299) : term317.
Proof. exact (EQ_MP (@lem1314961) (@lem1314832 h1)). Qed.
Lemma lem1314969 (x : nadd) (y : nadd) (z : nadd) : (term116 x y z) = (term117 x y z).
Proof. exact (@lem17045 (nadd_eq x y) (nadd_eq y z)). Qed.
Lemma lem1314970 (x : nadd) (z : nadd) : (nadd_eq x z) = (nadd_eq x z).
Proof. exact (eq_refl (nadd_eq x z)). Qed.
Lemma lem1314971 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1314972 (x : nadd) (y : nadd) (z : nadd) : (term118 x y z) = (term119 x y z).
Proof. exact (MK_COMB (@lem1314971) (@lem1314969 x y z)). Qed.
Lemma lem1314973 (y : nadd) (x : nadd) (z : nadd) : (term120 y x z) = (term121 y x z).
Proof. exact (MK_COMB (@lem1314972 x y z) (@lem1314970 x z)). Qed.
Lemma lem1314974 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term120 y x z).
Proof. exact (@lem17265 (term14 x y z) (nadd_eq x z)). Qed.
Lemma lem1314975 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term121 y x z).
Proof. exact (TRANS (@lem1314974 y x z) (@lem1314973 y x z)). Qed.
Lemma lem1314976 (y : nadd) (x : nadd) : (term55 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1314975 y x z)). Qed.
Lemma lem1314977 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314978 (y : nadd) (x : nadd) : (term11 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1314977) (@lem1314976 y x)). Qed.
Lemma lem1314979 (x : nadd) : (term56 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1314978 y x)). Qed.
Lemma lem1314980 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1314981 (x : nadd) : (term9 x) = (term125 x).
Proof. exact (MK_COMB (@lem1314980) (@lem1314979 x)). Qed.
Lemma lem1314982 : term57 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1314981 x)). Qed.
Lemma lem1314983 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315044 : term7 = term127.
Proof. exact (MK_COMB (@lem1314983) (@lem1314982)). Qed.
Lemma lem1315045 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1315044) (@lem1314833 h1)). Qed.
Lemma lem1315046 (y : nadd) (x : nadd) : (term231 y x) = (term231 y x).
Proof. exact (eq_refl (term231 y x)). Qed.
Lemma lem1315047 (x : nadd) : (term232 x) = (term232 x).
Proof. exact (fun_ext (fun y : nadd => @lem1315046 y x)). Qed.
Lemma lem1315048 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315049 (x : nadd) : (term233 x) = (term233 x).
Proof. exact (MK_COMB (@lem1315048) (@lem1315047 x)). Qed.
Lemma lem1315050 : term234 = term234.
Proof. exact (fun_ext (fun x : nadd => @lem1315049 x)). Qed.
Lemma lem1315051 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315064 : term208 = term208.
Proof. exact (MK_COMB (@lem1315051) (@lem1315050)). Qed.
Lemma lem1315065 (h1 : term208) : term208.
Proof. exact (EQ_MP (@lem1315064) (@lem1314834 h1)). Qed.
Lemma lem1315066 (x : nadd) (y : nadd) (z : nadd) : (term443 x y z) = (term443 x y z).
Proof. exact (eq_refl (term443 x y z)). Qed.
Lemma lem1315067 (x : nadd) (y : nadd) : (term444 x y) = (term444 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1315066 x y z)). Qed.
Lemma lem1315068 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315069 (x : nadd) (y : nadd) : (term445 x y) = (term445 x y).
Proof. exact (MK_COMB (@lem1315068) (@lem1315067 x y)). Qed.
Lemma lem1315070 (x : nadd) : (term446 x) = (term446 x).
Proof. exact (fun_ext (fun y : nadd => @lem1315069 x y)). Qed.
Lemma lem1315071 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315072 (x : nadd) : (term447 x) = (term447 x).
Proof. exact (MK_COMB (@lem1315071) (@lem1315070 x)). Qed.
Lemma lem1315073 : term448 = term448.
Proof. exact (fun_ext (fun x : nadd => @lem1315072 x)). Qed.
Lemma lem1315074 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315091 : term417 = term417.
Proof. exact (MK_COMB (@lem1315074) (@lem1315073)). Qed.
Lemma lem1315092 (h1 : term417) : term417.
Proof. exact (EQ_MP (@lem1315091) (@lem1314835 h1)). Qed.
Lemma lem1315154 (x : nadd) (y : nadd) (h1 : term410 x y) : term410 x y.
Proof. exact (h1). Qed.
Lemma lem1315159 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1315160 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1315159 x)). Qed.
Lemma lem1315161 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315162 : term301 = term301.
Proof. exact (MK_COMB (@lem1315161) (@lem1315160)). Qed.
Lemma lem1315163 (h1 : term301) : term301.
Proof. exact (EQ_MP (@lem1315162) (@lem1314872 h1)). Qed.
Lemma lem1315196 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term308 x y x' y') = (term308 x y x' y').
Proof. exact (eq_refl (term308 x y x' y')). Qed.
Lemma lem1315197 (x : nadd) (y : nadd) (x' : nadd) : (term310 x y x') = (term310 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1315196 x y x' y')). Qed.
Lemma lem1315198 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315199 (x : nadd) (y : nadd) (x' : nadd) : (term311 x y x') = (term311 x y x').
Proof. exact (MK_COMB (@lem1315198) (@lem1315197 x y x')). Qed.
Lemma lem1315200 (x : nadd) (x' : nadd) : (term312 x x') = (term312 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1315199 x y x')). Qed.
Lemma lem1315201 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315202 (x : nadd) (x' : nadd) : (term313 x x') = (term313 x x').
Proof. exact (MK_COMB (@lem1315201) (@lem1315200 x x')). Qed.
Lemma lem1315203 (x : nadd) : (term314 x) = (term314 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1315202 x x')). Qed.
Lemma lem1315204 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315205 (x : nadd) : (term315 x) = (term315 x).
Proof. exact (MK_COMB (@lem1315204) (@lem1315203 x)). Qed.
Lemma lem1315206 : term316 = term316.
Proof. exact (fun_ext (fun x : nadd => @lem1315205 x)). Qed.
Lemma lem1315207 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315208 : term317 = term317.
Proof. exact (MK_COMB (@lem1315207) (@lem1315206)). Qed.
Lemma lem1315209 (h1 : term299) : term317.
Proof. exact (EQ_MP (@lem1315208) (@lem1314962 h1)). Qed.
Lemma lem1315234 (y : nadd) (x : nadd) (z : nadd) : (term121 y x z) = (term121 y x z).
Proof. exact (eq_refl (term121 y x z)). Qed.
Lemma lem1315235 (y : nadd) (x : nadd) : (term122 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1315234 y x z)). Qed.
Lemma lem1315236 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315237 (y : nadd) (x : nadd) : (term123 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1315236) (@lem1315235 y x)). Qed.
Lemma lem1315238 (x : nadd) : (term124 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1315237 y x)). Qed.
Lemma lem1315239 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315240 (x : nadd) : (term125 x) = (term125 x).
Proof. exact (MK_COMB (@lem1315239) (@lem1315238 x)). Qed.
Lemma lem1315241 : term126 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1315240 x)). Qed.
Lemma lem1315242 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315243 : term127 = term127.
Proof. exact (MK_COMB (@lem1315242) (@lem1315241)). Qed.
Lemma lem1315244 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1315243) (@lem1315045 h1)). Qed.
Lemma lem1315257 (y : nadd) (x : nadd) : (term231 y x) = (term231 y x).
Proof. exact (eq_refl (term231 y x)). Qed.
Lemma lem1315258 (x : nadd) : (term232 x) = (term232 x).
Proof. exact (fun_ext (fun y : nadd => @lem1315257 y x)). Qed.
Lemma lem1315259 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315260 (x : nadd) : (term233 x) = (term233 x).
Proof. exact (MK_COMB (@lem1315259) (@lem1315258 x)). Qed.
Lemma lem1315261 : term234 = term234.
Proof. exact (fun_ext (fun x : nadd => @lem1315260 x)). Qed.
Lemma lem1315262 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315263 : term208 = term208.
Proof. exact (MK_COMB (@lem1315262) (@lem1315261)). Qed.
Lemma lem1315264 (h1 : term208) : term208.
Proof. exact (EQ_MP (@lem1315263) (@lem1315065 h1)). Qed.
Lemma lem1315285 (x : nadd) (y : nadd) (z : nadd) : (term443 x y z) = (term443 x y z).
Proof. exact (eq_refl (term443 x y z)). Qed.
Lemma lem1315286 (x : nadd) (y : nadd) : (term444 x y) = (term444 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1315285 x y z)). Qed.
Lemma lem1315287 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315288 (x : nadd) (y : nadd) : (term445 x y) = (term445 x y).
Proof. exact (MK_COMB (@lem1315287) (@lem1315286 x y)). Qed.
Lemma lem1315289 (x : nadd) : (term446 x) = (term446 x).
Proof. exact (fun_ext (fun y : nadd => @lem1315288 x y)). Qed.
Lemma lem1315290 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315291 (x : nadd) : (term447 x) = (term447 x).
Proof. exact (MK_COMB (@lem1315290) (@lem1315289 x)). Qed.
Lemma lem1315292 : term448 = term448.
Proof. exact (fun_ext (fun x : nadd => @lem1315291 x)). Qed.
Lemma lem1315293 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315294 : term417 = term417.
Proof. exact (MK_COMB (@lem1315293) (@lem1315292)). Qed.
Lemma lem1315295 (h1 : term417) : term417.
Proof. exact (EQ_MP (@lem1315294) (@lem1315092 h1)). Qed.
Lemma lem1315311 (x : nadd) (y : nadd) (h1 : term410 x y) : term410 x y.
Proof. exact (h1). Qed.
Lemma lem1315313 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1315314 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1315313 x)). Qed.
Lemma lem1315315 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315317 : term301 = term301.
Proof. exact (MK_COMB (@lem1315315) (@lem1315314)). Qed.
Lemma lem1315318 (h1 : term301) : term301.
Proof. exact (EQ_MP (@lem1315317) (@lem1315163 h1)). Qed.
Lemma lem1315332 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term308 x y x' y') = (term308 x y x' y').
Proof. exact (eq_refl (term308 x y x' y')). Qed.
Lemma lem1315333 (x : nadd) (y : nadd) (x' : nadd) : (term310 x y x') = (term310 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1315332 x y x' y')). Qed.
Lemma lem1315334 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315335 (x : nadd) (y : nadd) (x' : nadd) : (term311 x y x') = (term311 x y x').
Proof. exact (MK_COMB (@lem1315334) (@lem1315333 x y x')). Qed.
Lemma lem1315336 (x : nadd) (x' : nadd) : (term312 x x') = (term312 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1315335 x y x')). Qed.
Lemma lem1315337 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315338 (x : nadd) (x' : nadd) : (term313 x x') = (term313 x x').
Proof. exact (MK_COMB (@lem1315337) (@lem1315336 x x')). Qed.
Lemma lem1315339 (x : nadd) : (term314 x) = (term314 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1315338 x x')). Qed.
Lemma lem1315340 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315341 (x : nadd) : (term315 x) = (term315 x).
Proof. exact (MK_COMB (@lem1315340) (@lem1315339 x)). Qed.
Lemma lem1315342 : term316 = term316.
Proof. exact (fun_ext (fun x : nadd => @lem1315341 x)). Qed.
Lemma lem1315343 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315345 : term317 = term317.
Proof. exact (MK_COMB (@lem1315343) (@lem1315342)). Qed.
Lemma lem1315346 (h1 : term299) : term317.
Proof. exact (EQ_MP (@lem1315345) (@lem1315209 h1)). Qed.
Lemma lem1315360 (y : nadd) (x : nadd) (z : nadd) : (term121 y x z) = (term121 y x z).
Proof. exact (eq_refl (term121 y x z)). Qed.
Lemma lem1315361 (y : nadd) (x : nadd) : (term122 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1315360 y x z)). Qed.
Lemma lem1315362 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315363 (y : nadd) (x : nadd) : (term123 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1315362) (@lem1315361 y x)). Qed.
Lemma lem1315364 (x : nadd) : (term124 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1315363 y x)). Qed.
Lemma lem1315365 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315366 (x : nadd) : (term125 x) = (term125 x).
Proof. exact (MK_COMB (@lem1315365) (@lem1315364 x)). Qed.
Lemma lem1315367 : term126 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1315366 x)). Qed.
Lemma lem1315368 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315370 : term127 = term127.
Proof. exact (MK_COMB (@lem1315368) (@lem1315367)). Qed.
Lemma lem1315371 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1315370) (@lem1315244 h1)). Qed.
Lemma lem1315373 (y : nadd) (x : nadd) : (term231 y x) = (term231 y x).
Proof. exact (eq_refl (term231 y x)). Qed.
Lemma lem1315374 (x : nadd) : (term232 x) = (term232 x).
Proof. exact (fun_ext (fun y : nadd => @lem1315373 y x)). Qed.
Lemma lem1315375 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315376 (x : nadd) : (term233 x) = (term233 x).
Proof. exact (MK_COMB (@lem1315375) (@lem1315374 x)). Qed.
Lemma lem1315377 : term234 = term234.
Proof. exact (fun_ext (fun x : nadd => @lem1315376 x)). Qed.
Lemma lem1315378 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315380 : term208 = term208.
Proof. exact (MK_COMB (@lem1315378) (@lem1315377)). Qed.
Lemma lem1315381 (h1 : term208) : term208.
Proof. exact (EQ_MP (@lem1315380) (@lem1315264 h1)). Qed.
Lemma lem1315383 (x : nadd) (y : nadd) (z : nadd) : (term443 x y z) = (term443 x y z).
Proof. exact (eq_refl (term443 x y z)). Qed.
Lemma lem1315384 (x : nadd) (y : nadd) : (term444 x y) = (term444 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1315383 x y z)). Qed.
Lemma lem1315385 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315386 (x : nadd) (y : nadd) : (term445 x y) = (term445 x y).
Proof. exact (MK_COMB (@lem1315385) (@lem1315384 x y)). Qed.
Lemma lem1315387 (x : nadd) : (term446 x) = (term446 x).
Proof. exact (fun_ext (fun y : nadd => @lem1315386 x y)). Qed.
Lemma lem1315388 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315389 (x : nadd) : (term447 x) = (term447 x).
Proof. exact (MK_COMB (@lem1315388) (@lem1315387 x)). Qed.
Lemma lem1315390 : term448 = term448.
Proof. exact (fun_ext (fun x : nadd => @lem1315389 x)). Qed.
Lemma lem1315391 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315393 : term417 = term417.
Proof. exact (MK_COMB (@lem1315391) (@lem1315390)). Qed.
Lemma lem1315394 (h1 : term417) : term417.
Proof. exact (EQ_MP (@lem1315393) (@lem1315295 h1)). Qed.
Lemma lem1315395 (_23389 : nadd) (h1 : term301) : term167 _23389.
Proof. exact (@lem1315318 h1 _23389). Qed.
Lemma lem1315396 (_23389 : nadd) : (term167 _23389) = (nadd_eq _23389 _23389).
Proof. exact (eq_refl (term167 _23389)). Qed.
Lemma lem1315398 (_23390 : nadd) (h1 : term299) : term326 _23390.
Proof. exact (@lem1315346 h1 _23390). Qed.
Lemma lem1315399 (_23390 : nadd) : (term326 _23390) = (term315 _23390).
Proof. exact (eq_refl (term326 _23390)). Qed.
Lemma lem1315400 (_23390 : nadd) (h1 : term299) : term315 _23390.
Proof. exact (EQ_MP (@lem1315399 _23390) (@lem1315398 _23390 h1)). Qed.
Lemma lem1315401 (_23390 : nadd) (_23391 : nadd) (h1 : term299) : term327 _23390 _23391.
Proof. exact (@lem1315400 _23390 h1 _23391). Qed.
Lemma lem1315402 (_23390 : nadd) (_23391 : nadd) : (term327 _23390 _23391) = (term313 _23390 _23391).
Proof. exact (eq_refl (term327 _23390 _23391)). Qed.
Lemma lem1315403 (_23390 : nadd) (_23391 : nadd) (h1 : term299) : term313 _23390 _23391.
Proof. exact (EQ_MP (@lem1315402 _23390 _23391) (@lem1315401 _23390 _23391 h1)). Qed.
Lemma lem1315404 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (h1 : term299) : term328 _23390 _23391 _23392.
Proof. exact (@lem1315403 _23390 _23391 h1 _23392). Qed.
Lemma lem1315405 (_23390 : nadd) (_23392 : nadd) (_23391 : nadd) : (term328 _23390 _23391 _23392) = (term311 _23390 _23392 _23391).
Proof. exact (eq_refl (term328 _23390 _23391 _23392)). Qed.
Lemma lem1315406 (_23390 : nadd) (_23392 : nadd) (_23391 : nadd) (h1 : term299) : term311 _23390 _23392 _23391.
Proof. exact (EQ_MP (@lem1315405 _23390 _23392 _23391) (@lem1315404 _23390 _23391 _23392 h1)). Qed.
Lemma lem1315407 (_23390 : nadd) (_23392 : nadd) (_23391 : nadd) (_23393 : nadd) (h1 : term299) : term329 _23390 _23392 _23391 _23393.
Proof. exact (@lem1315406 _23390 _23392 _23391 h1 _23393). Qed.
Lemma lem1315408 (_23390 : nadd) (_23392 : nadd) (_23391 : nadd) (_23393 : nadd) : (term329 _23390 _23392 _23391 _23393) = (term308 _23390 _23392 _23391 _23393).
Proof. exact (eq_refl (term329 _23390 _23392 _23391 _23393)). Qed.
Lemma lem1315409 (_23390 : nadd) (_23392 : nadd) (_23391 : nadd) (_23393 : nadd) (h1 : term299) : term308 _23390 _23392 _23391 _23393.
Proof. exact (EQ_MP (@lem1315408 _23390 _23392 _23391 _23393) (@lem1315407 _23390 _23392 _23391 _23393 h1)). Qed.
Lemma lem1315410 (_23394 : nadd) (h1 : term7) : term128 _23394.
Proof. exact (@lem1315371 h1 _23394). Qed.
Lemma lem1315411 (_23394 : nadd) : (term128 _23394) = (term125 _23394).
Proof. exact (eq_refl (term128 _23394)). Qed.
Lemma lem1315412 (_23394 : nadd) (h1 : term7) : term125 _23394.
Proof. exact (EQ_MP (@lem1315411 _23394) (@lem1315410 _23394 h1)). Qed.
Lemma lem1315413 (_23394 : nadd) (_23395 : nadd) (h1 : term7) : term129 _23394 _23395.
Proof. exact (@lem1315412 _23394 h1 _23395). Qed.
Lemma lem1315414 (_23395 : nadd) (_23394 : nadd) : (term129 _23394 _23395) = (term123 _23395 _23394).
Proof. exact (eq_refl (term129 _23394 _23395)). Qed.
Lemma lem1315415 (_23395 : nadd) (_23394 : nadd) (h1 : term7) : term123 _23395 _23394.
Proof. exact (EQ_MP (@lem1315414 _23395 _23394) (@lem1315413 _23394 _23395 h1)). Qed.
Lemma lem1315416 (_23395 : nadd) (_23394 : nadd) (_23396 : nadd) (h1 : term7) : term130 _23395 _23394 _23396.
Proof. exact (@lem1315415 _23395 _23394 h1 _23396). Qed.
Lemma lem1315417 (_23395 : nadd) (_23394 : nadd) (_23396 : nadd) : (term130 _23395 _23394 _23396) = (term121 _23395 _23394 _23396).
Proof. exact (eq_refl (term130 _23395 _23394 _23396)). Qed.
Lemma lem1315418 (_23395 : nadd) (_23394 : nadd) (_23396 : nadd) (h1 : term7) : term121 _23395 _23394 _23396.
Proof. exact (EQ_MP (@lem1315417 _23395 _23394 _23396) (@lem1315416 _23395 _23394 _23396 h1)). Qed.
Lemma lem1315419 (_23397 : nadd) (h1 : term208) : term239 _23397.
Proof. exact (@lem1315381 h1 _23397). Qed.
Lemma lem1315420 (_23397 : nadd) : (term239 _23397) = (term233 _23397).
Proof. exact (eq_refl (term239 _23397)). Qed.
Lemma lem1315421 (_23397 : nadd) (h1 : term208) : term233 _23397.
Proof. exact (EQ_MP (@lem1315420 _23397) (@lem1315419 _23397 h1)). Qed.
Lemma lem1315422 (_23397 : nadd) (_23398 : nadd) (h1 : term208) : term240 _23397 _23398.
Proof. exact (@lem1315421 _23397 h1 _23398). Qed.
Lemma lem1315423 (_23398 : nadd) (_23397 : nadd) : (term240 _23397 _23398) = (term231 _23398 _23397).
Proof. exact (eq_refl (term240 _23397 _23398)). Qed.
Lemma lem1315425 (_23399 : nadd) (h1 : term417) : term449 _23399.
Proof. exact (@lem1315394 h1 _23399). Qed.
Lemma lem1315426 (_23399 : nadd) : (term449 _23399) = (term447 _23399).
Proof. exact (eq_refl (term449 _23399)). Qed.
Lemma lem1315427 (_23399 : nadd) (h1 : term417) : term447 _23399.
Proof. exact (EQ_MP (@lem1315426 _23399) (@lem1315425 _23399 h1)). Qed.
Lemma lem1315428 (_23399 : nadd) (_23400 : nadd) (h1 : term417) : term450 _23399 _23400.
Proof. exact (@lem1315427 _23399 h1 _23400). Qed.
Lemma lem1315429 (_23399 : nadd) (_23400 : nadd) : (term450 _23399 _23400) = (term445 _23399 _23400).
Proof. exact (eq_refl (term450 _23399 _23400)). Qed.
Lemma lem1315430 (_23399 : nadd) (_23400 : nadd) (h1 : term417) : term445 _23399 _23400.
Proof. exact (EQ_MP (@lem1315429 _23399 _23400) (@lem1315428 _23399 _23400 h1)). Qed.
Lemma lem1315431 (_23399 : nadd) (_23400 : nadd) (_23401 : nadd) (h1 : term417) : term451 _23399 _23400 _23401.
Proof. exact (@lem1315430 _23399 _23400 h1 _23401). Qed.
Lemma lem1315432 (_23399 : nadd) (_23400 : nadd) (_23401 : nadd) : (term451 _23399 _23400 _23401) = (term443 _23399 _23400 _23401).
Proof. exact (eq_refl (term451 _23399 _23400 _23401)). Qed.
Lemma lem1315441 (x : nadd) (y : nadd) (h1 : term410 x y) : term410 x y.
Proof. exact (h1). Qed.
Lemma lem1315454 (_23390 : nadd) (_23392 : nadd) (_23391 : nadd) (_23393 : nadd) : (term308 _23390 _23392 _23391 _23393) = (term331 _23390 _23392 _23391 _23393).
Proof. exact (@lem1309042 (term132 _23390 _23391) (term132 _23392 _23393) (term304 _23390 _23392 _23391 _23393)). Qed.
Lemma lem1315455 (_23390 : nadd) (_23392 : nadd) (_23391 : nadd) (_23393 : nadd) (h1 : term299) : term331 _23390 _23392 _23391 _23393.
Proof. exact (EQ_MP (@lem1315454 _23390 _23392 _23391 _23393) (@lem1315409 _23390 _23392 _23391 _23393 h1)). Qed.
Lemma lem1315466 (_23395 : nadd) (_23394 : nadd) (_23396 : nadd) : (term121 _23395 _23394 _23396) = (term131 _23395 _23394 _23396).
Proof. exact (@lem1309042 (term132 _23394 _23395) (term132 _23395 _23396) (nadd_eq _23394 _23396)). Qed.
Lemma lem1315467 (_23395 : nadd) (_23394 : nadd) (_23396 : nadd) (h1 : term7) : term131 _23395 _23394 _23396.
Proof. exact (EQ_MP (@lem1315466 _23395 _23394 _23396) (@lem1315418 _23395 _23394 _23396 h1)). Qed.
Lemma lem1315473 (_23398 : nadd) (_23397 : nadd) (h1 : term208) : term231 _23398 _23397.
Proof. exact (EQ_MP (@lem1315423 _23398 _23397) (@lem1315422 _23397 _23398 h1)). Qed.
Lemma lem1315474 (x : nadd) (y : nadd) (h1 : term208) : term452 x y.
Proof. exact (@lem1315473 (nadd_inv x) (term354 y) h1). Qed.
Lemma lem1315475 (x : nadd) (y : nadd) (h1 : term208) : term453 x y.
Proof. exact (fun h0 : term454 x y => @lem1315474 x y h1). Qed.
Lemma lem1315477 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1315478 (x : nadd) (y : nadd) : (term453 x y) = (term452 x y).
Proof. exact (@lem1315477 (term452 x y)). Qed.
Lemma lem1315479 (x : nadd) (y : nadd) (h1 : term208) : term452 x y.
Proof. exact (EQ_MP (@lem1315478 x y) (@lem1315475 x y h1)). Qed.
Lemma lem1315481 (_23389 : nadd) (h1 : term301) : nadd_eq _23389 _23389.
Proof. exact (EQ_MP (@lem1315396 _23389) (@lem1315395 _23389 h1)). Qed.
Lemma lem1315482 (x : nadd) (h1 : term301) : term332 x.
Proof. exact (@lem1315481 (nadd_inv x) h1). Qed.
Lemma lem1315483 (x : nadd) (h1 : term301) : term333 x.
Proof. exact (fun h0 : term334 x => @lem1315482 x h1). Qed.
Lemma lem1315485 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1315486 (x : nadd) : (term333 x) = (term332 x).
Proof. exact (@lem1315485 (term332 x)). Qed.
Lemma lem1315487 (x : nadd) (h1 : term301) : term332 x.
Proof. exact (EQ_MP (@lem1315486 x) (@lem1315483 x h1)). Qed.
Lemma lem1315489 (_23398 : nadd) (_23397 : nadd) (h1 : term208) : term231 _23398 _23397.
Proof. exact (EQ_MP (@lem1315423 _23398 _23397) (@lem1315422 _23397 _23398 h1)). Qed.
Lemma lem1315490 (y : nadd) (h1 : term208) : term455 y.
Proof. exact (@lem1315489 y (nadd_inv y) h1). Qed.
Lemma lem1315491 (y : nadd) (h1 : term208) : term456 y.
Proof. exact (fun h0 : term457 y => @lem1315490 y h1). Qed.
Lemma lem1315493 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1315494 (y : nadd) : (term456 y) = (term455 y).
Proof. exact (@lem1315493 (term455 y)). Qed.
Lemma lem1315495 (y : nadd) (h1 : term208) : term455 y.
Proof. exact (EQ_MP (@lem1315494 y) (@lem1315491 y h1)). Qed.
Lemma lem1315511 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1315512 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : (term341 _23390 _23392 _23391 _23393) = (term342 _23390 _23391 _23392 _23393).
Proof. exact (@lem1315511 (term304 _23390 _23392 _23391 _23393) (term132 _23392 _23393)). Qed.
Lemma lem1315518 (_23390 : nadd) (_23391 : nadd) : (term146 _23390 _23391) = (term146 _23390 _23391).
Proof. exact (eq_refl (term146 _23390 _23391)). Qed.
Lemma lem1315519 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : (term331 _23390 _23392 _23391 _23393) = (term343 _23390 _23391 _23392 _23393).
Proof. exact (MK_COMB (@lem1315518 _23390 _23391) (@lem1315512 _23390 _23391 _23392 _23393)). Qed.
Lemma lem1315523 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1315524 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : (term343 _23390 _23391 _23392 _23393) = (term344 _23390 _23391 _23392 _23393).
Proof. exact (@lem1315523 (term304 _23390 _23392 _23391 _23393) (term132 _23390 _23391) (term132 _23392 _23393)). Qed.
Lemma lem1315540 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : (term331 _23390 _23392 _23391 _23393) = (term344 _23390 _23391 _23392 _23393).
Proof. exact (TRANS (@lem1315519 _23390 _23391 _23392 _23393) (@lem1315524 _23390 _23391 _23392 _23393)). Qed.
Lemma lem1315541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1315542 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : (term345 _23390 _23392 _23391 _23393) = (term346 _23390 _23391 _23392 _23393).
Proof. exact (MK_COMB (@lem1315541) (@lem1315540 _23390 _23391 _23392 _23393)). Qed.
Lemma lem1315558 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : (term344 _23390 _23391 _23392 _23393) = (term344 _23390 _23391 _23392 _23393).
Proof. exact (eq_refl (term344 _23390 _23391 _23392 _23393)). Qed.
Lemma lem1315559 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : ((term331 _23390 _23392 _23391 _23393) = (term344 _23390 _23391 _23392 _23393)) = ((term344 _23390 _23391 _23392 _23393) = (term344 _23390 _23391 _23392 _23393)).
Proof. exact (MK_COMB (@lem1315542 _23390 _23391 _23392 _23393) (@lem1315558 _23390 _23391 _23392 _23393)). Qed.
Lemma lem1315561 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1315562 (x : Prop) : (x = x) = True.
Proof. exact (@lem1315561 Prop x). Qed.
Lemma lem1315563 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : ((term344 _23390 _23391 _23392 _23393) = (term344 _23390 _23391 _23392 _23393)) = True.
Proof. exact (@lem1315562 (term344 _23390 _23391 _23392 _23393)). Qed.
Lemma lem1315564 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : ((term331 _23390 _23392 _23391 _23393) = (term344 _23390 _23391 _23392 _23393)) = True.
Proof. exact (TRANS (@lem1315559 _23390 _23391 _23392 _23393) (@lem1315563 _23390 _23391 _23392 _23393)). Qed.
Lemma lem1315565 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : True = ((term331 _23390 _23392 _23391 _23393) = (term344 _23390 _23391 _23392 _23393)).
Proof. exact (SYM (@lem1315564 _23390 _23391 _23392 _23393)). Qed.
Lemma lem1315566 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : (term331 _23390 _23392 _23391 _23393) = (term344 _23390 _23391 _23392 _23393).
Proof. exact (EQ_MP (@lem1315565 _23390 _23391 _23392 _23393) (@lem0)). Qed.
Lemma lem1315567 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) (h1 : term299) : term344 _23390 _23391 _23392 _23393.
Proof. exact (EQ_MP (@lem1315566 _23390 _23391 _23392 _23393) (@lem1315455 _23390 _23392 _23391 _23393 h1)). Qed.
Lemma lem1315569 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1315570 (_23390 : nadd) (_23392 : nadd) (_23391 : nadd) (_23393 : nadd) : (term344 _23390 _23391 _23392 _23393) = (term347 _23390 _23392 _23391 _23393).
Proof. exact (@lem1315569 (term303 _23390 _23391 _23392 _23393) (term304 _23390 _23392 _23391 _23393)). Qed.
Lemma lem1315572 (a : Prop) (b : Prop) : (term152 a b) = (term153 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1315573 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : (term348 _23390 _23391 _23392 _23393) = (term349 _23390 _23391 _23392 _23393).
Proof. exact (@lem1315572 (term132 _23390 _23391) (term132 _23392 _23393)). Qed.
Lemma lem1315575 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1315576 (_23390 : nadd) (_23391 : nadd) : (term140 _23390 _23391) = (nadd_eq _23390 _23391).
Proof. exact (@lem1315575 (nadd_eq _23390 _23391)). Qed.
Lemma lem1315577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1315578 (_23390 : nadd) (_23391 : nadd) : (term156 _23390 _23391) = (term157 _23390 _23391).
Proof. exact (MK_COMB (@lem1315577) (@lem1315576 _23390 _23391)). Qed.
Lemma lem1315580 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1315581 (_23392 : nadd) (_23393 : nadd) : (term140 _23392 _23393) = (nadd_eq _23392 _23393).
Proof. exact (@lem1315580 (nadd_eq _23392 _23393)). Qed.
Lemma lem1315582 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : (term349 _23390 _23391 _23392 _23393) = (term309 _23390 _23391 _23392 _23393).
Proof. exact (MK_COMB (@lem1315578 _23390 _23391) (@lem1315581 _23392 _23393)). Qed.
Lemma lem1315583 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : (term348 _23390 _23391 _23392 _23393) = (term309 _23390 _23391 _23392 _23393).
Proof. exact (TRANS (@lem1315573 _23390 _23391 _23392 _23393) (@lem1315582 _23390 _23391 _23392 _23393)). Qed.
Lemma lem1315584 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1315585 (_23390 : nadd) (_23391 : nadd) (_23392 : nadd) (_23393 : nadd) : (term350 _23390 _23391 _23392 _23393) = (term351 _23390 _23391 _23392 _23393).
Proof. exact (MK_COMB (@lem1315584) (@lem1315583 _23390 _23391 _23392 _23393)). Qed.
Lemma lem1315586 (_23390 : nadd) (_23392 : nadd) (_23391 : nadd) (_23393 : nadd) : (term304 _23390 _23392 _23391 _23393) = (term304 _23390 _23392 _23391 _23393).
Proof. exact (eq_refl (term304 _23390 _23392 _23391 _23393)). Qed.
Lemma lem1315587 (_23390 : nadd) (_23392 : nadd) (_23391 : nadd) (_23393 : nadd) : (term347 _23390 _23392 _23391 _23393) = (term291 _23390 _23392 _23391 _23393).
Proof. exact (MK_COMB (@lem1315585 _23390 _23391 _23392 _23393) (@lem1315586 _23390 _23392 _23391 _23393)). Qed.
Lemma lem1315588 (_23390 : nadd) (_23392 : nadd) (_23391 : nadd) (_23393 : nadd) : (term344 _23390 _23391 _23392 _23393) = (term291 _23390 _23392 _23391 _23393).
Proof. exact (TRANS (@lem1315570 _23390 _23392 _23391 _23393) (@lem1315587 _23390 _23392 _23391 _23393)). Qed.
Lemma lem1315590 (x : nadd) (y : nadd) (h1 : term208) (h2 : term301) : term458 x y.
Proof. exact (conj (@lem1315487 x h2) (@lem1315495 y h1)). Qed.
Lemma lem1315592 (_23390 : nadd) (_23392 : nadd) (_23391 : nadd) (_23393 : nadd) (h1 : term299) : term291 _23390 _23392 _23391 _23393.
Proof. exact (EQ_MP (@lem1315588 _23390 _23392 _23391 _23393) (@lem1315567 _23390 _23391 _23392 _23393 h1)). Qed.
Lemma lem1315593 (x : nadd) (y : nadd) (h1 : term299) : term459 x y.
Proof. exact (@lem1315592 (nadd_inv x) (term354 y) (nadd_inv x) (term460 y) h1). Qed.
Lemma lem1315596 (x : nadd) (y : nadd) (h1 : term299) (h2 : term208) (h3 : term301) : term461 x y.
Proof. exact (@lem1315593 x y h1 (@lem1315590 x y h2 h3)). Qed.
Lemma lem1315597 (x : nadd) (y : nadd) (h1 : term299) (h2 : term208) (h3 : term301) : term462 x y.
Proof. exact (fun h0 : term463 x y => @lem1315596 x y h1 h2 h3). Qed.
Lemma lem1315599 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1315600 (x : nadd) (y : nadd) : (term462 x y) = (term461 x y).
Proof. exact (@lem1315599 (term461 x y)). Qed.
Lemma lem1315601 (x : nadd) (y : nadd) (h1 : term299) (h2 : term208) (h3 : term301) : term461 x y.
Proof. exact (EQ_MP (@lem1315600 x y) (@lem1315597 x y h1 h2 h3)). Qed.
Lemma lem1315603 (_23399 : nadd) (_23400 : nadd) (_23401 : nadd) (h1 : term417) : term443 _23399 _23400 _23401.
Proof. exact (EQ_MP (@lem1315432 _23399 _23400 _23401) (@lem1315431 _23399 _23400 _23401 h1)). Qed.
Lemma lem1315604 (x : nadd) (y : nadd) (h1 : term417) : term464 x y.
Proof. exact (@lem1315603 (nadd_inv x) y (nadd_inv y) h1). Qed.
Lemma lem1315605 (x : nadd) (y : nadd) (h1 : term417) : term465 x y.
Proof. exact (fun h0 : term466 x y => @lem1315604 x y h1). Qed.
Lemma lem1315607 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1315608 (x : nadd) (y : nadd) : (term465 x y) = (term464 x y).
Proof. exact (@lem1315607 (term464 x y)). Qed.
Lemma lem1315609 (x : nadd) (y : nadd) (h1 : term417) : term464 x y.
Proof. exact (EQ_MP (@lem1315608 x y) (@lem1315605 x y h1)). Qed.
Lemma lem1315625 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1315626 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : (term144 _23395 _23394 _23396) = (term145 _23394 _23395 _23396).
Proof. exact (@lem1315625 (nadd_eq _23394 _23396) (term132 _23395 _23396)). Qed.
Lemma lem1315632 (_23394 : nadd) (_23395 : nadd) : (term146 _23394 _23395) = (term146 _23394 _23395).
Proof. exact (eq_refl (term146 _23394 _23395)). Qed.
Lemma lem1315633 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : (term131 _23395 _23394 _23396) = (term147 _23394 _23395 _23396).
Proof. exact (MK_COMB (@lem1315632 _23394 _23395) (@lem1315626 _23394 _23395 _23396)). Qed.
Lemma lem1315637 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1315638 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : (term147 _23394 _23395 _23396) = (term148 _23394 _23395 _23396).
Proof. exact (@lem1315637 (nadd_eq _23394 _23396) (term132 _23394 _23395) (term132 _23395 _23396)). Qed.
Lemma lem1315654 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : (term131 _23395 _23394 _23396) = (term148 _23394 _23395 _23396).
Proof. exact (TRANS (@lem1315633 _23394 _23395 _23396) (@lem1315638 _23394 _23395 _23396)). Qed.
Lemma lem1315655 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1315656 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : (term149 _23395 _23394 _23396) = (term150 _23394 _23395 _23396).
Proof. exact (MK_COMB (@lem1315655) (@lem1315654 _23394 _23395 _23396)). Qed.
Lemma lem1315672 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : (term148 _23394 _23395 _23396) = (term148 _23394 _23395 _23396).
Proof. exact (eq_refl (term148 _23394 _23395 _23396)). Qed.
Lemma lem1315673 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : ((term131 _23395 _23394 _23396) = (term148 _23394 _23395 _23396)) = ((term148 _23394 _23395 _23396) = (term148 _23394 _23395 _23396)).
Proof. exact (MK_COMB (@lem1315656 _23394 _23395 _23396) (@lem1315672 _23394 _23395 _23396)). Qed.
Lemma lem1315675 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1315676 (x : Prop) : (x = x) = True.
Proof. exact (@lem1315675 Prop x). Qed.
Lemma lem1315677 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : ((term148 _23394 _23395 _23396) = (term148 _23394 _23395 _23396)) = True.
Proof. exact (@lem1315676 (term148 _23394 _23395 _23396)). Qed.
Lemma lem1315678 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : ((term131 _23395 _23394 _23396) = (term148 _23394 _23395 _23396)) = True.
Proof. exact (TRANS (@lem1315673 _23394 _23395 _23396) (@lem1315677 _23394 _23395 _23396)). Qed.
Lemma lem1315679 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : True = ((term131 _23395 _23394 _23396) = (term148 _23394 _23395 _23396)).
Proof. exact (SYM (@lem1315678 _23394 _23395 _23396)). Qed.
Lemma lem1315680 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : (term131 _23395 _23394 _23396) = (term148 _23394 _23395 _23396).
Proof. exact (EQ_MP (@lem1315679 _23394 _23395 _23396) (@lem0)). Qed.
Lemma lem1315681 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) (h1 : term7) : term148 _23394 _23395 _23396.
Proof. exact (EQ_MP (@lem1315680 _23394 _23395 _23396) (@lem1315467 _23395 _23394 _23396 h1)). Qed.
Lemma lem1315683 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1315684 (_23395 : nadd) (_23394 : nadd) (_23396 : nadd) : (term148 _23394 _23395 _23396) = (term151 _23395 _23394 _23396).
Proof. exact (@lem1315683 (term117 _23394 _23395 _23396) (nadd_eq _23394 _23396)). Qed.
Lemma lem1315686 (a : Prop) (b : Prop) : (term152 a b) = (term153 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1315687 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : (term154 _23394 _23395 _23396) = (term155 _23394 _23395 _23396).
Proof. exact (@lem1315686 (term132 _23394 _23395) (term132 _23395 _23396)). Qed.
Lemma lem1315689 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1315690 (_23394 : nadd) (_23395 : nadd) : (term140 _23394 _23395) = (nadd_eq _23394 _23395).
Proof. exact (@lem1315689 (nadd_eq _23394 _23395)). Qed.
Lemma lem1315691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1315692 (_23394 : nadd) (_23395 : nadd) : (term156 _23394 _23395) = (term157 _23394 _23395).
Proof. exact (MK_COMB (@lem1315691) (@lem1315690 _23394 _23395)). Qed.
Lemma lem1315694 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1315695 (_23395 : nadd) (_23396 : nadd) : (term140 _23395 _23396) = (nadd_eq _23395 _23396).
Proof. exact (@lem1315694 (nadd_eq _23395 _23396)). Qed.
Lemma lem1315696 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : (term155 _23394 _23395 _23396) = (term14 _23394 _23395 _23396).
Proof. exact (MK_COMB (@lem1315692 _23394 _23395) (@lem1315695 _23395 _23396)). Qed.
Lemma lem1315697 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : (term154 _23394 _23395 _23396) = (term14 _23394 _23395 _23396).
Proof. exact (TRANS (@lem1315687 _23394 _23395 _23396) (@lem1315696 _23394 _23395 _23396)). Qed.
Lemma lem1315698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1315699 (_23394 : nadd) (_23395 : nadd) (_23396 : nadd) : (term158 _23394 _23395 _23396) = (term159 _23394 _23395 _23396).
Proof. exact (MK_COMB (@lem1315698) (@lem1315697 _23394 _23395 _23396)). Qed.
Lemma lem1315700 (_23394 : nadd) (_23396 : nadd) : (nadd_eq _23394 _23396) = (nadd_eq _23394 _23396).
Proof. exact (eq_refl (nadd_eq _23394 _23396)). Qed.
Lemma lem1315701 (_23395 : nadd) (_23394 : nadd) (_23396 : nadd) : (term151 _23395 _23394 _23396) = (term13 _23395 _23394 _23396).
Proof. exact (MK_COMB (@lem1315699 _23394 _23395 _23396) (@lem1315700 _23394 _23396)). Qed.
Lemma lem1315702 (_23395 : nadd) (_23394 : nadd) (_23396 : nadd) : (term148 _23394 _23395 _23396) = (term13 _23395 _23394 _23396).
Proof. exact (TRANS (@lem1315684 _23395 _23394 _23396) (@lem1315701 _23395 _23394 _23396)). Qed.
Lemma lem1315704 (x : nadd) (y : nadd) (h1 : term299) (h2 : term417) (h3 : term208) (h4 : term301) : term467 x y.
Proof. exact (conj (@lem1315601 x y h1 h3 h4) (@lem1315609 x y h2)). Qed.
Lemma lem1315706 (_23395 : nadd) (_23394 : nadd) (_23396 : nadd) (h1 : term7) : term13 _23395 _23394 _23396.
Proof. exact (EQ_MP (@lem1315702 _23395 _23394 _23396) (@lem1315681 _23394 _23395 _23396 h1)). Qed.
Lemma lem1315707 (x : nadd) (y : nadd) (h1 : term7) : term468 x y.
Proof. exact (@lem1315706 (term469 x y) (term360 x y) (term470 x y) h1). Qed.
Lemma lem1315710 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) : term471 x y.
Proof. exact (@lem1315707 x y h2 (@lem1315704 x y h1 h3 h4 h5)). Qed.
Lemma lem1315711 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) : term472 x y.
Proof. exact (fun h0 : term473 x y => @lem1315710 x y h1 h2 h3 h4 h5). Qed.
Lemma lem1315713 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1315714 (x : nadd) (y : nadd) : (term472 x y) = (term471 x y).
Proof. exact (@lem1315713 (term471 x y)). Qed.
Lemma lem1315715 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) : term471 x y.
Proof. exact (EQ_MP (@lem1315714 x y) (@lem1315711 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1315717 (_23398 : nadd) (_23397 : nadd) (h1 : term208) : term231 _23398 _23397.
Proof. exact (EQ_MP (@lem1315423 _23398 _23397) (@lem1315422 _23397 _23398 h1)). Qed.
Lemma lem1315718 (x : nadd) (y : nadd) (h1 : term208) : term474 x y.
Proof. exact (@lem1315717 (nadd_inv y) (term397 x y) h1). Qed.
Lemma lem1315719 (x : nadd) (y : nadd) (h1 : term208) : term475 x y.
Proof. exact (fun h0 : term476 x y => @lem1315718 x y h1). Qed.
Lemma lem1315721 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1315722 (x : nadd) (y : nadd) : (term475 x y) = (term474 x y).
Proof. exact (@lem1315721 (term474 x y)). Qed.
Lemma lem1315723 (x : nadd) (y : nadd) (h1 : term208) : term474 x y.
Proof. exact (EQ_MP (@lem1315722 x y) (@lem1315719 x y h1)). Qed.
Lemma lem1315724 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) : term477 x y.
Proof. exact (conj (@lem1315715 x y h1 h2 h3 h4 h5) (@lem1315723 x y h4)). Qed.
Lemma lem1315726 (_23395 : nadd) (_23394 : nadd) (_23396 : nadd) (h1 : term7) : term13 _23395 _23394 _23396.
Proof. exact (EQ_MP (@lem1315702 _23395 _23394 _23396) (@lem1315681 _23394 _23395 _23396 h1)). Qed.
Lemma lem1315727 (x : nadd) (y : nadd) (h1 : term7) : term478 x y.
Proof. exact (@lem1315726 (term470 x y) (term360 x y) (term402 x y) h1). Qed.
Lemma lem1315730 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) : term479 x y.
Proof. exact (@lem1315727 x y h2 (@lem1315724 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1315731 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) : term480 x y.
Proof. exact (fun h0 : term481 x y => @lem1315730 x y h1 h2 h3 h4 h5). Qed.
Lemma lem1315733 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1315734 (x : nadd) (y : nadd) : (term480 x y) = (term479 x y).
Proof. exact (@lem1315733 (term479 x y)). Qed.
Lemma lem1315735 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) : term479 x y.
Proof. exact (EQ_MP (@lem1315734 x y) (@lem1315731 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1315736 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) : term482 x y.
Proof. exact (conj (@lem1315479 x y h4) (@lem1315735 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1315738 (_23395 : nadd) (_23394 : nadd) (_23396 : nadd) (h1 : term7) : term13 _23395 _23394 _23396.
Proof. exact (EQ_MP (@lem1315702 _23395 _23394 _23396) (@lem1315681 _23394 _23395 _23396 h1)). Qed.
Lemma lem1315739 (x : nadd) (y : nadd) (h1 : term7) : term483 x y.
Proof. exact (@lem1315738 (term360 x y) (term484 y x) (term402 x y) h1). Qed.
Lemma lem1315742 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) : term408 x y.
Proof. exact (@lem1315739 x y h2 (@lem1315736 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1315743 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) : term485 x y.
Proof. exact (fun h0 : term410 x y => @lem1315742 x y h1 h2 h3 h4 h5). Qed.
Lemma lem1315745 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1315746 (x : nadd) (y : nadd) : (term485 x y) = (term408 x y).
Proof. exact (@lem1315745 (term408 x y)). Qed.
Lemma lem1315747 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) : term408 x y.
Proof. exact (EQ_MP (@lem1315746 x y) (@lem1315743 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1315750 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1315752 (x : nadd) (y : nadd) : (term410 x y) = (term486 x y).
Proof. exact (@lem1315750 (term408 x y)). Qed.
Lemma lem1315755 (x : nadd) (y : nadd) (h1 : term410 x y) : term486 x y.
Proof. exact (EQ_MP (@lem1315752 x y) (@lem1315441 x y h1)). Qed.
Lemma lem1315758 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (@lem1315755 x y h6 (@lem1315747 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1315759 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : term164.
Proof. exact (fun h0 : ~ False => @lem1315758 x y h1 h2 h3 h4 h5 h6). Qed.
Lemma lem1315761 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1315762 : term164 = False.
Proof. exact (@lem1315761 False). Qed.
Lemma lem1315763 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315762) (@lem1315759 x y h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1315764 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : (term410 x y) = False.
Proof. exact (prop_ext (fun h7 : term410 x y => @lem1315763 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1315441 x y h6)). Qed.
Lemma lem1315765 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315764 x y h1 h2 h3 h4 h5 h6) (@lem1315441 x y h6)). Qed.
Lemma lem1315766 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : (term410 x y) = False.
Proof. exact (prop_ext (fun h7 : term410 x y => @lem1315765 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1315311 x y h6)). Qed.
Lemma lem1315767 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315766 x y h1 h2 h3 h4 h5 h6) (@lem1315311 x y h6)). Qed.
Lemma lem1315768 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : term417 = False.
Proof. exact (prop_ext (fun h7 : term417 => @lem1315767 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1315394 h3)). Qed.
Lemma lem1315769 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315768 x y h1 h2 h3 h4 h5 h6) (@lem1315394 h3)). Qed.
Lemma lem1315770 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : term208 = False.
Proof. exact (prop_ext (fun h7 : term208 => @lem1315769 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1315381 h4)). Qed.
Lemma lem1315771 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315770 x y h1 h2 h3 h4 h5 h6) (@lem1315381 h4)). Qed.
Lemma lem1315772 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : term301 = False.
Proof. exact (prop_ext (fun h7 : term301 => @lem1315771 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1315318 h5)). Qed.
Lemma lem1315773 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315772 x y h1 h2 h3 h4 h5 h6) (@lem1315318 h5)). Qed.
Lemma lem1315774 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : (term410 x y) = False.
Proof. exact (prop_ext (fun h7 : term410 x y => @lem1315773 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1315311 x y h6)). Qed.
Lemma lem1315775 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315774 x y h1 h2 h3 h4 h5 h6) (@lem1315311 x y h6)). Qed.
Lemma lem1315776 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : term417 = False.
Proof. exact (prop_ext (fun h7 : term417 => @lem1315775 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1315295 h3)). Qed.
Lemma lem1315777 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315776 x y h1 h2 h3 h4 h5 h6) (@lem1315295 h3)). Qed.
Lemma lem1315778 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : term208 = False.
Proof. exact (prop_ext (fun h7 : term208 => @lem1315777 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1315264 h4)). Qed.
Lemma lem1315779 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315778 x y h1 h2 h3 h4 h5 h6) (@lem1315264 h4)). Qed.
Lemma lem1315780 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : term301 = False.
Proof. exact (prop_ext (fun h7 : term301 => @lem1315779 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1315163 h5)). Qed.
Lemma lem1315781 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315780 x y h1 h2 h3 h4 h5 h6) (@lem1315163 h5)). Qed.
Lemma lem1315782 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : (term410 x y) = False.
Proof. exact (prop_ext (fun h7 : term410 x y => @lem1315781 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1315154 x y h6)). Qed.
Lemma lem1315783 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315782 x y h1 h2 h3 h4 h5 h6) (@lem1315154 x y h6)). Qed.
Lemma lem1315784 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : term417 = False.
Proof. exact (prop_ext (fun h7 : term417 => @lem1315783 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1315092 h3)). Qed.
Lemma lem1315785 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315784 x y h1 h2 h3 h4 h5 h6) (@lem1315092 h3)). Qed.
Lemma lem1315786 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : term208 = False.
Proof. exact (prop_ext (fun h7 : term208 => @lem1315785 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1315065 h4)). Qed.
Lemma lem1315787 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315786 x y h1 h2 h3 h4 h5 h6) (@lem1315065 h4)). Qed.
Lemma lem1315788 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : term301 = False.
Proof. exact (prop_ext (fun h7 : term301 => @lem1315787 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1314872 h5)). Qed.
Lemma lem1315789 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315788 x y h1 h2 h3 h4 h5 h6) (@lem1314872 h5)). Qed.
Lemma lem1315790 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : (term410 x y) = False.
Proof. exact (prop_ext (fun h7 : term410 x y => @lem1315789 x y h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem1314859 x y h6)). Qed.
Lemma lem1315791 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term417) (h4 : term208) (h5 : term301) (h6 : term410 x y) : False.
Proof. exact (EQ_MP (@lem1315790 x y h1 h2 h3 h4 h5 h6) (@lem1314859 x y h6)). Qed.
Lemma lem1315792 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term208) (h4 : term301) (h5 : term410 x y) : term415.
Proof. exact (fun h0 : term417 => @lem1315791 x y h1 h2 h0 h3 h4 h5). Qed.
Lemma lem1315793 : term415 = term416.
Proof. exact (@lem69 term417). Qed.
Lemma lem1315794 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term208) (h4 : term301) (h5 : term410 x y) : term416.
Proof. exact (EQ_MP (@lem1315793) (@lem1315792 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1315795 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term301) (h4 : term410 x y) : term420.
Proof. exact (fun h0 : term208 => @lem1315794 x y h1 h2 h0 h3 h4). Qed.
Lemma lem1315796 (x : nadd) (y : nadd) (h1 : term299) (h2 : term301) (h3 : term410 x y) : term422.
Proof. exact (fun h0 : term7 => @lem1315795 x y h1 h0 h2 h3). Qed.
Lemma lem1315797 (x : nadd) (y : nadd) (h1 : term301) (h2 : term410 x y) : term424.
Proof. exact (fun h0 : term299 => @lem1315796 x y h0 h1 h2). Qed.
Lemma lem1315798 (x : nadd) (y : nadd) (h1 : term410 x y) : term426.
Proof. exact (fun h0 : term301 => @lem1315797 x y h0 h1). Qed.
Lemma lem1315799 (x : nadd) (y : nadd) : term429 x y.
Proof. exact (fun h0 : term410 x y => @lem1315798 x y h0). Qed.
Lemma lem1315800 (x : nadd) (y : nadd) : term431 x y.
Proof. exact (fun h0 : term27 y => @lem1315799 x y). Qed.
Lemma lem1315801 (x : nadd) (y : nadd) : term433 x y.
Proof. exact (fun h0 : term27 x => @lem1315800 x y). Qed.
Lemma lem1315802 (x : nadd) (y : nadd) : term434 x y.
Proof. exact (fun h0 : nadd_eq x y => @lem1315801 x y). Qed.
Lemma lem1315807 (y : nadd) : term438 y.
Proof. exact (fun x : nadd => @lem1315802 x y). Qed.
Lemma lem1315812 : term442.
Proof. exact (fun y : nadd => @lem1315807 y). Qed.
Lemma lem1315813 : term441.
Proof. exact (EQ_MP (@lem1314826) (@lem1315812)). Qed.
Lemma lem1315814 (y : nadd) : term487 y.
Proof. exact (@lem1315813 y). Qed.
Lemma lem1315815 (y : nadd) : (term487 y) = (term437 y).
Proof. exact (eq_refl (term487 y)). Qed.
Lemma lem1315816 (y : nadd) : term437 y.
Proof. exact (EQ_MP (@lem1315815 y) (@lem1315814 y)). Qed.
Lemma lem1315817 (y : nadd) (x : nadd) : term488 y x.
Proof. exact (@lem1315816 y x). Qed.
Lemma lem1315818 (x : nadd) (y : nadd) : (term488 y x) = (term411 x y).
Proof. exact (eq_refl (term488 y x)). Qed.
Lemma lem1315819 (x : nadd) (y : nadd) : term411 x y.
Proof. exact (EQ_MP (@lem1315818 x y) (@lem1315817 y x)). Qed.
Lemma lem1315821 (x : nadd) (y : nadd) : term411 x y.
Proof. exact (@lem1314469 x y (@lem1315819 x y)). Qed.
Lemma lem1315822 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term432 x y.
Proof. exact (@lem1315821 x y (@lem1309210 x y h1)). Qed.
Lemma lem1315823 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) : term430 x y.
Proof. exact (@lem1315822 x y h2 (@lem1309209 x h1)). Qed.
Lemma lem1315824 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term428 x y.
Proof. exact (@lem1315823 x y h1 h3 (@lem1310360 y h2)). Qed.
Lemma lem1315825 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term410 x y) (h4 : nadd_eq x y) : term425.
Proof. exact (@lem1315824 x y h1 h2 h4 (@lem1314454 x y h3)). Qed.
Lemma lem1315826 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term410 x y) (h4 : nadd_eq x y) : term423.
Proof. exact (@lem1315825 x y h1 h2 h3 h4 (@lem1267990)). Qed.
Lemma lem1315827 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term410 x y) (h4 : nadd_eq x y) : term421.
Proof. exact (@lem1315826 x y h1 h2 h3 h4 (@lem1279298)). Qed.
Lemma lem1315828 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term410 x y) (h4 : nadd_eq x y) : term419.
Proof. exact (@lem1315827 x y h1 h2 h3 h4 (@lem1268295)). Qed.
Lemma lem1315829 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term410 x y) (h4 : nadd_eq x y) : term415.
Proof. exact (@lem1315828 x y h1 h2 h3 h4 (@lem1278399)). Qed.
Lemma lem1315830 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term410 x y) (h4 : nadd_eq x y) : False.
Proof. exact (@lem1315829 x y h1 h2 h3 h4 (@lem1278498)). Qed.
Lemma lem1315831 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term410 x y) (h4 : nadd_eq x y) : (term410 x y) = False.
Proof. exact (prop_ext (fun h5 : term410 x y => @lem1315830 x y h1 h2 h3 h4) (fun h5 : False => @lem1314454 x y h3)). Qed.
Lemma lem1315832 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term410 x y) (h4 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1315831 x y h1 h2 h3 h4) (@lem1314454 x y h3)). Qed.
Lemma lem1315833 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term409 x y.
Proof. exact (fun h0 : term410 x y => @lem1315832 x y h1 h2 h0 h3). Qed.
Lemma lem1315834 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term408 x y.
Proof. exact (EQ_MP (@lem1314453 x y) (@lem1315833 x y h1 h2 h3)). Qed.
Lemma lem1315836 (p : Prop) : p = (term28 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1315837 (y : nadd) (x : nadd) : (term489 y x) = (term490 y x).
Proof. exact (@lem1315836 (term489 y x)). Qed.
Lemma lem1315838 (y : nadd) (x : nadd) : (term490 y x) = (term489 y x).
Proof. exact (SYM (@lem1315837 y x)). Qed.
Lemma lem1315839 (y : nadd) (x : nadd) (h1 : term491 y x) : term491 y x.
Proof. exact (h1). Qed.
Lemma lem1315842 (y : nadd) (x : nadd) (h1 : term492 y x) : term492 y x.
Proof. exact (h1). Qed.
Lemma lem1315843 (y : nadd) (x : nadd) : term493 y x.
Proof. exact (fun h0 : term492 y x => @lem1315842 y x h0). Qed.
Lemma lem1315844 (y : nadd) (x : nadd) (h1 : term493 y x) : term493 y x.
Proof. exact (h1). Qed.
Lemma lem1315845 (y : nadd) (x : nadd) (h1 : term492 y x) : term492 y x.
Proof. exact (h1). Qed.
Lemma lem1315846 (y : nadd) (x : nadd) (h1 : term493 y x) (h2 : term492 y x) : term492 y x.
Proof. exact (@lem1315844 y x h1 (@lem1315845 y x h2)). Qed.
Lemma lem1315847 (y : nadd) (x : nadd) (h1 : term492 y x) : term494 y x.
Proof. exact (fun h0 : term493 y x => @lem1315846 y x h0 h1). Qed.
Lemma lem1315848 (y : nadd) (x : nadd) (h1 : term493 y x) : term493 y x.
Proof. exact (h1). Qed.
Lemma lem1315849 (y : nadd) (x : nadd) (h1 : term493 y x) (h2 : term492 y x) : term492 y x.
Proof. exact (@lem1315847 y x h2 (@lem1315848 y x h1)). Qed.
Lemma lem1315850 (y : nadd) (x : nadd) (h1 : term493 y x) : term493 y x.
Proof. exact (fun h0 : term492 y x => @lem1315849 y x h1 h0). Qed.
Lemma lem1315851 (y : nadd) (x : nadd) : term495 y x.
Proof. exact (fun h0 : term493 y x => @lem1315850 y x h0). Qed.
Lemma lem1315854 (y : nadd) (x : nadd) : term493 y x.
Proof. exact (@lem1315851 y x (@lem1315843 y x)). Qed.
Lemma lem1315934 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1315935 : term264 = term265.
Proof. exact (@lem1315934 term266). Qed.
Lemma lem1315942 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem1315943 : term268 = term269.
Proof. exact (MK_COMB (@lem1315942) (@lem1315935)). Qed.
Lemma lem1315946 : term270 = term270.
Proof. exact (eq_refl term270). Qed.
Lemma lem1315947 : term271 = term272.
Proof. exact (MK_COMB (@lem1315946) (@lem1315943)). Qed.
Lemma lem1315950 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem1315951 : term496 = term497.
Proof. exact (MK_COMB (@lem1315950) (@lem1315947)). Qed.
Lemma lem1315954 : term212 = term212.
Proof. exact (eq_refl term212). Qed.
Lemma lem1315955 : term498 = term499.
Proof. exact (MK_COMB (@lem1315954) (@lem1315951)). Qed.
Lemma lem1315958 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1315959 : term500 = term501.
Proof. exact (MK_COMB (@lem1315958) (@lem1315955)). Qed.
Lemma lem1315962 (y : nadd) (x : nadd) : (term502 y x) = (term502 y x).
Proof. exact (eq_refl (term502 y x)). Qed.
Lemma lem1315963 (y : nadd) (x : nadd) : (term503 y x) = (term504 y x).
Proof. exact (MK_COMB (@lem1315962 y x) (@lem1315959)). Qed.
Lemma lem1315966 (y : nadd) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem1315967 (y : nadd) (x : nadd) : (term505 y x) = (term506 y x).
Proof. exact (MK_COMB (@lem1315966 y) (@lem1315963 y x)). Qed.
Lemma lem1315970 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1315971 (y : nadd) (x : nadd) : (term507 y x) = (term508 y x).
Proof. exact (MK_COMB (@lem1315970 x) (@lem1315967 y x)). Qed.
Lemma lem1315974 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1315975 (y : nadd) (x : nadd) : (term492 y x) = (term509 y x).
Proof. exact (MK_COMB (@lem1315974 x y) (@lem1315971 y x)). Qed.
Lemma lem1315978 (x : nadd) : (term510 x) = (term511 x).
Proof. exact (fun_ext (fun y : nadd => @lem1315975 y x)). Qed.
Lemma lem1315979 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315980 (x : nadd) : (term512 x) = (term513 x).
Proof. exact (MK_COMB (@lem1315979) (@lem1315978 x)). Qed.
Lemma lem1315985 : term514 = term515.
Proof. exact (fun_ext (fun x : nadd => @lem1315980 x)). Qed.
Lemma lem1315986 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1315995 : term516 = term517.
Proof. exact (MK_COMB (@lem1315986) (@lem1315985)). Qed.
Lemma lem1316002 (x : nadd) : (term289 x) = (term289 x).
Proof. exact (eq_refl (term289 x)). Qed.
Lemma lem1316003 : term290 = term290.
Proof. exact (fun_ext (fun x : nadd => @lem1316002 x)). Qed.
Lemma lem1316004 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316005 : term266 = term266.
Proof. exact (MK_COMB (@lem1316004) (@lem1316003)). Qed.
Lemma lem1316006 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1316007 : term265 = term265.
Proof. exact (MK_COMB (@lem1316006) (@lem1316005)). Qed.
Lemma lem1316016 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term291 x y x' y') = (term291 x y x' y').
Proof. exact (eq_refl (term291 x y x' y')). Qed.
Lemma lem1316017 (x : nadd) (y : nadd) (x' : nadd) : (term292 x y x') = (term292 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1316016 x y x' y')). Qed.
Lemma lem1316018 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316019 (x : nadd) (y : nadd) (x' : nadd) : (term293 x y x') = (term293 x y x').
Proof. exact (MK_COMB (@lem1316018) (@lem1316017 x y x')). Qed.
Lemma lem1316020 (x : nadd) (x' : nadd) : (term294 x x') = (term294 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1316019 x y x')). Qed.
Lemma lem1316021 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316022 (x : nadd) (x' : nadd) : (term295 x x') = (term295 x x').
Proof. exact (MK_COMB (@lem1316021) (@lem1316020 x x')). Qed.
Lemma lem1316023 (x : nadd) : (term296 x) = (term296 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1316022 x x')). Qed.
Lemma lem1316024 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316025 (x : nadd) : (term297 x) = (term297 x).
Proof. exact (MK_COMB (@lem1316024) (@lem1316023 x)). Qed.
Lemma lem1316026 : term298 = term298.
Proof. exact (fun_ext (fun x : nadd => @lem1316025 x)). Qed.
Lemma lem1316027 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316028 : term299 = term299.
Proof. exact (MK_COMB (@lem1316027) (@lem1316026)). Qed.
Lemma lem1316029 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1316030 : term267 = term267.
Proof. exact (MK_COMB (@lem1316029) (@lem1316028)). Qed.
Lemma lem1316031 : term269 = term269.
Proof. exact (MK_COMB (@lem1316030) (@lem1316007)). Qed.
Lemma lem1316032 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1316033 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1316032 x)). Qed.
Lemma lem1316034 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316035 : term301 = term301.
Proof. exact (MK_COMB (@lem1316034) (@lem1316033)). Qed.
Lemma lem1316036 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1316037 : term270 = term270.
Proof. exact (MK_COMB (@lem1316036) (@lem1316035)). Qed.
Lemma lem1316038 : term272 = term272.
Proof. exact (MK_COMB (@lem1316037) (@lem1316031)). Qed.
Lemma lem1316039 (x : nadd) : (term235 x) = (term235 x).
Proof. exact (eq_refl (term235 x)). Qed.
Lemma lem1316040 : term236 = term236.
Proof. exact (fun_ext (fun x : nadd => @lem1316039 x)). Qed.
Lemma lem1316041 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316042 : term237 = term237.
Proof. exact (MK_COMB (@lem1316041) (@lem1316040)). Qed.
Lemma lem1316043 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1316044 : term209 = term209.
Proof. exact (MK_COMB (@lem1316043) (@lem1316042)). Qed.
Lemma lem1316045 : term497 = term497.
Proof. exact (MK_COMB (@lem1316044) (@lem1316038)). Qed.
Lemma lem1316054 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term13 y x z).
Proof. exact (eq_refl (term13 y x z)). Qed.
Lemma lem1316055 (y : nadd) (x : nadd) : (term55 y x) = (term55 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1316054 y x z)). Qed.
Lemma lem1316056 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316057 (y : nadd) (x : nadd) : (term11 y x) = (term11 y x).
Proof. exact (MK_COMB (@lem1316056) (@lem1316055 y x)). Qed.
Lemma lem1316058 (x : nadd) : (term56 x) = (term56 x).
Proof. exact (fun_ext (fun y : nadd => @lem1316057 y x)). Qed.
Lemma lem1316059 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316060 (x : nadd) : (term9 x) = (term9 x).
Proof. exact (MK_COMB (@lem1316059) (@lem1316058 x)). Qed.
Lemma lem1316061 : term57 = term57.
Proof. exact (fun_ext (fun x : nadd => @lem1316060 x)). Qed.
Lemma lem1316062 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316063 : term7 = term7.
Proof. exact (MK_COMB (@lem1316062) (@lem1316061)). Qed.
Lemma lem1316064 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1316065 : term212 = term212.
Proof. exact (MK_COMB (@lem1316064) (@lem1316063)). Qed.
Lemma lem1316066 : term499 = term499.
Proof. exact (MK_COMB (@lem1316065) (@lem1316045)). Qed.
Lemma lem1316071 (y : nadd) (x : nadd) : ((nadd_eq x y) = (nadd_eq y x)) = ((nadd_eq x y) = (nadd_eq y x)).
Proof. exact (eq_refl ((nadd_eq x y) = (nadd_eq y x))). Qed.
Lemma lem1316072 (x : nadd) : (term58 x) = (term58 x).
Proof. exact (fun_ext (fun y : nadd => @lem1316071 y x)). Qed.
Lemma lem1316073 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316074 (x : nadd) : (term59 x) = (term59 x).
Proof. exact (MK_COMB (@lem1316073) (@lem1316072 x)). Qed.
Lemma lem1316075 : term60 = term60.
Proof. exact (fun_ext (fun x : nadd => @lem1316074 x)). Qed.
Lemma lem1316076 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316077 : term61 = term61.
Proof. exact (MK_COMB (@lem1316076) (@lem1316075)). Qed.
Lemma lem1316078 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1316079 : term36 = term36.
Proof. exact (MK_COMB (@lem1316078) (@lem1316077)). Qed.
Lemma lem1316080 : term501 = term501.
Proof. exact (MK_COMB (@lem1316079) (@lem1316066)). Qed.
Lemma lem1316085 (y : nadd) (x : nadd) : (term502 y x) = (term502 y x).
Proof. exact (eq_refl (term502 y x)). Qed.
Lemma lem1316086 (y : nadd) (x : nadd) : (term504 y x) = (term504 y x).
Proof. exact (MK_COMB (@lem1316085 y x) (@lem1316080)). Qed.
Lemma lem1316091 (y : nadd) : (term39 y) = (term39 y).
Proof. exact (eq_refl (term39 y)). Qed.
Lemma lem1316092 (y : nadd) (x : nadd) : (term506 y x) = (term506 y x).
Proof. exact (MK_COMB (@lem1316091 y) (@lem1316086 y x)). Qed.
Lemma lem1316097 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1316098 (y : nadd) (x : nadd) : (term508 y x) = (term508 y x).
Proof. exact (MK_COMB (@lem1316097 x) (@lem1316092 y x)). Qed.
Lemma lem1316101 (x : nadd) (y : nadd) : (term45 x y) = (term45 x y).
Proof. exact (eq_refl (term45 x y)). Qed.
Lemma lem1316102 (y : nadd) (x : nadd) : (term509 y x) = (term509 y x).
Proof. exact (MK_COMB (@lem1316101 x y) (@lem1316098 y x)). Qed.
Lemma lem1316103 (x : nadd) : (term511 x) = (term511 x).
Proof. exact (fun_ext (fun y : nadd => @lem1316102 y x)). Qed.
Lemma lem1316104 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316105 (x : nadd) : (term513 x) = (term513 x).
Proof. exact (MK_COMB (@lem1316104) (@lem1316103 x)). Qed.
Lemma lem1316106 : term515 = term515.
Proof. exact (fun_ext (fun x : nadd => @lem1316105 x)). Qed.
Lemma lem1316107 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316108 : term517 = term517.
Proof. exact (MK_COMB (@lem1316107) (@lem1316106)). Qed.
Lemma lem1316223 : term516 = term517.
Proof. exact (TRANS (@lem1315995) (@lem1316108)). Qed.
Lemma lem1316224 : term517 = term516.
Proof. exact (SYM (@lem1316223)). Qed.
Lemma lem1316229 (h1 : term61) : term61.
Proof. exact (h1). Qed.
Lemma lem1316230 (h1 : term7) : term7.
Proof. exact (h1). Qed.
Lemma lem1316231 (h1 : term237) : term237.
Proof. exact (h1). Qed.
Lemma lem1316232 (h1 : term301) : term301.
Proof. exact (h1). Qed.
Lemma lem1316233 (h1 : term299) : term299.
Proof. exact (h1). Qed.
Lemma lem1316234 (h1 : term266) : term266.
Proof. exact (h1). Qed.
Lemma lem1316252 (y : nadd) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1316258 (y : nadd) (x : nadd) (h1 : term491 y x) : term491 y x.
Proof. exact (h1). Qed.
Lemma lem1316273 (y : nadd) (x : nadd) : ((nadd_eq x y) = (nadd_eq y x)) = (term62 y x).
Proof. exact (@lem17784 (nadd_eq x y) (nadd_eq y x)). Qed.
Lemma lem1316274 (x : nadd) : (term58 x) = (term63 x).
Proof. exact (fun_ext (fun y : nadd => @lem1316273 y x)). Qed.
Lemma lem1316275 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316276 (x : nadd) : (term59 x) = (term64 x).
Proof. exact (MK_COMB (@lem1316275) (@lem1316274 x)). Qed.
Lemma lem1316277 : term60 = term65.
Proof. exact (fun_ext (fun x : nadd => @lem1316276 x)). Qed.
Lemma lem1316278 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316279 : term61 = term66.
Proof. exact (MK_COMB (@lem1316278) (@lem1316277)). Qed.
Lemma lem1316285 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1316286 (P : nadd -> Prop) (Q : nadd -> Prop) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem1316285 nadd P Q). Qed.
Lemma lem1316287 (x : nadd) : (term71 x) = (term72 x).
Proof. exact (@lem1316286 (term73 x) (term74 x)). Qed.
Lemma lem1316288 (y : nadd) (x : nadd) : (term75 x y) = (term76 y x).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1316289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1316290 (y : nadd) (x : nadd) : (term77 x y) = (term78 y x).
Proof. exact (MK_COMB (@lem1316289) (@lem1316288 y x)). Qed.
Lemma lem1316291 (y : nadd) (x : nadd) : (term79 x y) = (term80 y x).
Proof. exact (eq_refl (term79 x y)). Qed.
Lemma lem1316292 (y : nadd) (x : nadd) : (term81 x y) = (term62 y x).
Proof. exact (MK_COMB (@lem1316290 y x) (@lem1316291 y x)). Qed.
Lemma lem1316293 (x : nadd) : (term82 x) = (term63 x).
Proof. exact (fun_ext (fun y : nadd => @lem1316292 y x)). Qed.
Lemma lem1316294 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316295 (x : nadd) : (term71 x) = (term64 x).
Proof. exact (MK_COMB (@lem1316294) (@lem1316293 x)). Qed.
Lemma lem1316296 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1316297 (x : nadd) : (term83 x) = (term84 x).
Proof. exact (MK_COMB (@lem1316296) (@lem1316295 x)). Qed.
Lemma lem1316298 (y : nadd) (x : nadd) : (term75 x y) = (term76 y x).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1316299 (x : nadd) : (term85 x) = (term73 x).
Proof. exact (fun_ext (fun y : nadd => @lem1316298 y x)). Qed.
Lemma lem1316300 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316301 (x : nadd) : (term86 x) = (term87 x).
Proof. exact (MK_COMB (@lem1316300) (@lem1316299 x)). Qed.
Lemma lem1316302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1316303 (x : nadd) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem1316302) (@lem1316301 x)). Qed.
Lemma lem1316304 (y : nadd) (x : nadd) : (term79 x y) = (term80 y x).
Proof. exact (eq_refl (term79 x y)). Qed.
Lemma lem1316305 (x : nadd) : (term90 x) = (term74 x).
Proof. exact (fun_ext (fun y : nadd => @lem1316304 y x)). Qed.
Lemma lem1316306 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316307 (x : nadd) : (term91 x) = (term92 x).
Proof. exact (MK_COMB (@lem1316306) (@lem1316305 x)). Qed.
Lemma lem1316308 (x : nadd) : (term72 x) = (term93 x).
Proof. exact (MK_COMB (@lem1316303 x) (@lem1316307 x)). Qed.
Lemma lem1316309 (x : nadd) : ((term71 x) = (term72 x)) = ((term64 x) = (term93 x)).
Proof. exact (MK_COMB (@lem1316297 x) (@lem1316308 x)). Qed.
Lemma lem1316310 (x : nadd) : (term64 x) = (term93 x).
Proof. exact (EQ_MP (@lem1316309 x) (@lem1316287 x)). Qed.
Lemma lem1316407 : term65 = term94.
Proof. exact (fun_ext (fun x : nadd => @lem1316310 x)). Qed.
Lemma lem1316408 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316409 : term66 = term95.
Proof. exact (MK_COMB (@lem1316408) (@lem1316407)). Qed.
Lemma lem1316411 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1316412 (P : nadd -> Prop) (Q : nadd -> Prop) : (term69 P Q) = (term70 P Q).
Proof. exact (@lem1316411 nadd P Q). Qed.
Lemma lem1316413 : term96 = term97.
Proof. exact (@lem1316412 term98 term99). Qed.
Lemma lem1316414 (x : nadd) : (term100 x) = (term87 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1316415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1316416 (x : nadd) : (term101 x) = (term89 x).
Proof. exact (MK_COMB (@lem1316415) (@lem1316414 x)). Qed.
Lemma lem1316417 (x : nadd) : (term102 x) = (term92 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1316418 (x : nadd) : (term103 x) = (term93 x).
Proof. exact (MK_COMB (@lem1316416 x) (@lem1316417 x)). Qed.
Lemma lem1316419 : term104 = term94.
Proof. exact (fun_ext (fun x : nadd => @lem1316418 x)). Qed.
Lemma lem1316420 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316421 : term96 = term95.
Proof. exact (MK_COMB (@lem1316420) (@lem1316419)). Qed.
Lemma lem1316422 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1316423 : term105 = term106.
Proof. exact (MK_COMB (@lem1316422) (@lem1316421)). Qed.
Lemma lem1316424 (x : nadd) : (term100 x) = (term87 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1316425 : term107 = term98.
Proof. exact (fun_ext (fun x : nadd => @lem1316424 x)). Qed.
Lemma lem1316426 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316427 : term108 = term109.
Proof. exact (MK_COMB (@lem1316426) (@lem1316425)). Qed.
Lemma lem1316428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1316429 : term110 = term111.
Proof. exact (MK_COMB (@lem1316428) (@lem1316427)). Qed.
Lemma lem1316430 (x : nadd) : (term102 x) = (term92 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1316431 : term112 = term99.
Proof. exact (fun_ext (fun x : nadd => @lem1316430 x)). Qed.
Lemma lem1316432 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316433 : term113 = term114.
Proof. exact (MK_COMB (@lem1316432) (@lem1316431)). Qed.
Lemma lem1316434 : term97 = term115.
Proof. exact (MK_COMB (@lem1316429) (@lem1316433)). Qed.
Lemma lem1316435 : (term96 = term97) = (term95 = term115).
Proof. exact (MK_COMB (@lem1316423) (@lem1316434)). Qed.
Lemma lem1316436 : term95 = term115.
Proof. exact (EQ_MP (@lem1316435) (@lem1316413)). Qed.
Lemma lem1316543 : term66 = term115.
Proof. exact (TRANS (@lem1316409) (@lem1316436)). Qed.
Lemma lem1316544 : term61 = term115.
Proof. exact (TRANS (@lem1316279) (@lem1316543)). Qed.
Lemma lem1316545 (h1 : term61) : term115.
Proof. exact (EQ_MP (@lem1316544) (@lem1316229 h1)). Qed.
Lemma lem1316552 (x : nadd) (y : nadd) (z : nadd) : (term116 x y z) = (term117 x y z).
Proof. exact (@lem17045 (nadd_eq x y) (nadd_eq y z)). Qed.
Lemma lem1316553 (x : nadd) (z : nadd) : (nadd_eq x z) = (nadd_eq x z).
Proof. exact (eq_refl (nadd_eq x z)). Qed.
Lemma lem1316554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1316555 (x : nadd) (y : nadd) (z : nadd) : (term118 x y z) = (term119 x y z).
Proof. exact (MK_COMB (@lem1316554) (@lem1316552 x y z)). Qed.
Lemma lem1316556 (y : nadd) (x : nadd) (z : nadd) : (term120 y x z) = (term121 y x z).
Proof. exact (MK_COMB (@lem1316555 x y z) (@lem1316553 x z)). Qed.
Lemma lem1316557 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term120 y x z).
Proof. exact (@lem17265 (term14 x y z) (nadd_eq x z)). Qed.
Lemma lem1316558 (y : nadd) (x : nadd) (z : nadd) : (term13 y x z) = (term121 y x z).
Proof. exact (TRANS (@lem1316557 y x z) (@lem1316556 y x z)). Qed.
Lemma lem1316559 (y : nadd) (x : nadd) : (term55 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1316558 y x z)). Qed.
Lemma lem1316560 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316561 (y : nadd) (x : nadd) : (term11 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1316560) (@lem1316559 y x)). Qed.
Lemma lem1316562 (x : nadd) : (term56 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1316561 y x)). Qed.
Lemma lem1316563 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316564 (x : nadd) : (term9 x) = (term125 x).
Proof. exact (MK_COMB (@lem1316563) (@lem1316562 x)). Qed.
Lemma lem1316565 : term57 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1316564 x)). Qed.
Lemma lem1316566 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316627 : term7 = term127.
Proof. exact (MK_COMB (@lem1316566) (@lem1316565)). Qed.
Lemma lem1316628 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1316627) (@lem1316230 h1)). Qed.
Lemma lem1316629 (x : nadd) : (term235 x) = (term235 x).
Proof. exact (eq_refl (term235 x)). Qed.
Lemma lem1316630 : term236 = term236.
Proof. exact (fun_ext (fun x : nadd => @lem1316629 x)). Qed.
Lemma lem1316631 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316640 : term237 = term237.
Proof. exact (MK_COMB (@lem1316631) (@lem1316630)). Qed.
Lemma lem1316641 (h1 : term237) : term237.
Proof. exact (EQ_MP (@lem1316640) (@lem1316231 h1)). Qed.
Lemma lem1316642 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1316643 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1316642 x)). Qed.
Lemma lem1316644 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316653 : term301 = term301.
Proof. exact (MK_COMB (@lem1316644) (@lem1316643)). Qed.
Lemma lem1316654 (h1 : term301) : term301.
Proof. exact (EQ_MP (@lem1316653) (@lem1316232 h1)). Qed.
Lemma lem1316661 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term302 x x' y y') = (term303 x x' y y').
Proof. exact (@lem17045 (nadd_eq x x') (nadd_eq y y')). Qed.
Lemma lem1316662 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term304 x y x' y') = (term304 x y x' y').
Proof. exact (eq_refl (term304 x y x' y')). Qed.
Lemma lem1316663 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1316664 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term305 x x' y y') = (term306 x x' y y').
Proof. exact (MK_COMB (@lem1316663) (@lem1316661 x x' y y')). Qed.
Lemma lem1316665 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term307 x y x' y') = (term308 x y x' y').
Proof. exact (MK_COMB (@lem1316664 x x' y y') (@lem1316662 x y x' y')). Qed.
Lemma lem1316666 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term291 x y x' y') = (term307 x y x' y').
Proof. exact (@lem17265 (term309 x x' y y') (term304 x y x' y')). Qed.
Lemma lem1316667 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term291 x y x' y') = (term308 x y x' y').
Proof. exact (TRANS (@lem1316666 x y x' y') (@lem1316665 x y x' y')). Qed.
Lemma lem1316668 (x : nadd) (y : nadd) (x' : nadd) : (term292 x y x') = (term310 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1316667 x y x' y')). Qed.
Lemma lem1316669 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316670 (x : nadd) (y : nadd) (x' : nadd) : (term293 x y x') = (term311 x y x').
Proof. exact (MK_COMB (@lem1316669) (@lem1316668 x y x')). Qed.
Lemma lem1316671 (x : nadd) (x' : nadd) : (term294 x x') = (term312 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1316670 x y x')). Qed.
Lemma lem1316672 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316673 (x : nadd) (x' : nadd) : (term295 x x') = (term313 x x').
Proof. exact (MK_COMB (@lem1316672) (@lem1316671 x x')). Qed.
Lemma lem1316674 (x : nadd) : (term296 x) = (term314 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1316673 x x')). Qed.
Lemma lem1316675 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316676 (x : nadd) : (term297 x) = (term315 x).
Proof. exact (MK_COMB (@lem1316675) (@lem1316674 x)). Qed.
Lemma lem1316677 : term298 = term316.
Proof. exact (fun_ext (fun x : nadd => @lem1316676 x)). Qed.
Lemma lem1316678 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316743 : term299 = term317.
Proof. exact (MK_COMB (@lem1316678) (@lem1316677)). Qed.
Lemma lem1316744 (h1 : term299) : term317.
Proof. exact (EQ_MP (@lem1316743) (@lem1316233 h1)). Qed.
Lemma lem1316747 (x : nadd) : (term318 x) = (term25 x).
Proof. exact (@lem16933 (term25 x)). Qed.
Lemma lem1316748 (x : nadd) : (term319 x) = (term319 x).
Proof. exact (eq_refl (term319 x)). Qed.
Lemma lem1316749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1316750 (x : nadd) : (term320 x) = (term321 x).
Proof. exact (MK_COMB (@lem1316749) (@lem1316747 x)). Qed.
Lemma lem1316751 (x : nadd) : (term322 x) = (term323 x).
Proof. exact (MK_COMB (@lem1316750 x) (@lem1316748 x)). Qed.
Lemma lem1316752 (x : nadd) : (term289 x) = (term322 x).
Proof. exact (@lem17265 (term27 x) (term319 x)). Qed.
Lemma lem1316753 (x : nadd) : (term289 x) = (term323 x).
Proof. exact (TRANS (@lem1316752 x) (@lem1316751 x)). Qed.
Lemma lem1316754 : term290 = term324.
Proof. exact (fun_ext (fun x : nadd => @lem1316753 x)). Qed.
Lemma lem1316755 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316808 : term266 = term325.
Proof. exact (MK_COMB (@lem1316755) (@lem1316754)). Qed.
Lemma lem1316809 (h1 : term266) : term325.
Proof. exact (EQ_MP (@lem1316808) (@lem1316234 h1)). Qed.
Lemma lem1316839 (y : nadd) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1316861 (y : nadd) (x : nadd) (h1 : term491 y x) : term491 y x.
Proof. exact (h1). Qed.
Lemma lem1316876 (y : nadd) (x : nadd) : (term80 y x) = (term80 y x).
Proof. exact (eq_refl (term80 y x)). Qed.
Lemma lem1316877 (x : nadd) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : nadd => @lem1316876 y x)). Qed.
Lemma lem1316878 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316879 (x : nadd) : (term92 x) = (term92 x).
Proof. exact (MK_COMB (@lem1316878) (@lem1316877 x)). Qed.
Lemma lem1316880 : term99 = term99.
Proof. exact (fun_ext (fun x : nadd => @lem1316879 x)). Qed.
Lemma lem1316881 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316882 : term114 = term114.
Proof. exact (MK_COMB (@lem1316881) (@lem1316880)). Qed.
Lemma lem1316897 (y : nadd) (x : nadd) : (term76 y x) = (term76 y x).
Proof. exact (eq_refl (term76 y x)). Qed.
Lemma lem1316898 (x : nadd) : (term73 x) = (term73 x).
Proof. exact (fun_ext (fun y : nadd => @lem1316897 y x)). Qed.
Lemma lem1316899 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316900 (x : nadd) : (term87 x) = (term87 x).
Proof. exact (MK_COMB (@lem1316899) (@lem1316898 x)). Qed.
Lemma lem1316901 : term98 = term98.
Proof. exact (fun_ext (fun x : nadd => @lem1316900 x)). Qed.
Lemma lem1316902 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316903 : term109 = term109.
Proof. exact (MK_COMB (@lem1316902) (@lem1316901)). Qed.
Lemma lem1316904 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1316905 : term111 = term111.
Proof. exact (MK_COMB (@lem1316904) (@lem1316903)). Qed.
Lemma lem1316906 : term115 = term115.
Proof. exact (MK_COMB (@lem1316905) (@lem1316882)). Qed.
Lemma lem1316907 (h1 : term61) : term115.
Proof. exact (EQ_MP (@lem1316906) (@lem1316545 h1)). Qed.
Lemma lem1316932 (y : nadd) (x : nadd) (z : nadd) : (term121 y x z) = (term121 y x z).
Proof. exact (eq_refl (term121 y x z)). Qed.
Lemma lem1316933 (y : nadd) (x : nadd) : (term122 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1316932 y x z)). Qed.
Lemma lem1316934 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316935 (y : nadd) (x : nadd) : (term123 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1316934) (@lem1316933 y x)). Qed.
Lemma lem1316936 (x : nadd) : (term124 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1316935 y x)). Qed.
Lemma lem1316937 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316938 (x : nadd) : (term125 x) = (term125 x).
Proof. exact (MK_COMB (@lem1316937) (@lem1316936 x)). Qed.
Lemma lem1316939 : term126 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1316938 x)). Qed.
Lemma lem1316940 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316941 : term127 = term127.
Proof. exact (MK_COMB (@lem1316940) (@lem1316939)). Qed.
Lemma lem1316942 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1316941) (@lem1316628 h1)). Qed.
Lemma lem1316957 (x : nadd) : (term235 x) = (term235 x).
Proof. exact (eq_refl (term235 x)). Qed.
Lemma lem1316958 : term236 = term236.
Proof. exact (fun_ext (fun x : nadd => @lem1316957 x)). Qed.
Lemma lem1316959 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316960 : term237 = term237.
Proof. exact (MK_COMB (@lem1316959) (@lem1316958)). Qed.
Lemma lem1316961 (h1 : term237) : term237.
Proof. exact (EQ_MP (@lem1316960) (@lem1316641 h1)). Qed.
Lemma lem1316966 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1316967 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1316966 x)). Qed.
Lemma lem1316968 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1316969 : term301 = term301.
Proof. exact (MK_COMB (@lem1316968) (@lem1316967)). Qed.
Lemma lem1316970 (h1 : term301) : term301.
Proof. exact (EQ_MP (@lem1316969) (@lem1316654 h1)). Qed.
Lemma lem1317003 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term308 x y x' y') = (term308 x y x' y').
Proof. exact (eq_refl (term308 x y x' y')). Qed.
Lemma lem1317004 (x : nadd) (y : nadd) (x' : nadd) : (term310 x y x') = (term310 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1317003 x y x' y')). Qed.
Lemma lem1317005 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317006 (x : nadd) (y : nadd) (x' : nadd) : (term311 x y x') = (term311 x y x').
Proof. exact (MK_COMB (@lem1317005) (@lem1317004 x y x')). Qed.
Lemma lem1317007 (x : nadd) (x' : nadd) : (term312 x x') = (term312 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1317006 x y x')). Qed.
Lemma lem1317008 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317009 (x : nadd) (x' : nadd) : (term313 x x') = (term313 x x').
Proof. exact (MK_COMB (@lem1317008) (@lem1317007 x x')). Qed.
Lemma lem1317010 (x : nadd) : (term314 x) = (term314 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1317009 x x')). Qed.
Lemma lem1317011 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317012 (x : nadd) : (term315 x) = (term315 x).
Proof. exact (MK_COMB (@lem1317011) (@lem1317010 x)). Qed.
Lemma lem1317013 : term316 = term316.
Proof. exact (fun_ext (fun x : nadd => @lem1317012 x)). Qed.
Lemma lem1317014 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317015 : term317 = term317.
Proof. exact (MK_COMB (@lem1317014) (@lem1317013)). Qed.
Lemma lem1317016 (h1 : term299) : term317.
Proof. exact (EQ_MP (@lem1317015) (@lem1316744 h1)). Qed.
Lemma lem1317045 (x : nadd) : (term323 x) = (term323 x).
Proof. exact (eq_refl (term323 x)). Qed.
Lemma lem1317046 : term324 = term324.
Proof. exact (fun_ext (fun x : nadd => @lem1317045 x)). Qed.
Lemma lem1317047 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317048 : term325 = term325.
Proof. exact (MK_COMB (@lem1317047) (@lem1317046)). Qed.
Lemma lem1317049 (h1 : term266) : term325.
Proof. exact (EQ_MP (@lem1317048) (@lem1316809 h1)). Qed.
Lemma lem1317050 (h1 : term61) : term114.
Proof. exact (proj2 (@lem1316907 h1)). Qed.
Lemma lem1317063 (y : nadd) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1317067 (y : nadd) (x : nadd) (h1 : term491 y x) : term491 y x.
Proof. exact (h1). Qed.
Lemma lem1317081 (y : nadd) (x : nadd) (z : nadd) : (term121 y x z) = (term121 y x z).
Proof. exact (eq_refl (term121 y x z)). Qed.
Lemma lem1317082 (y : nadd) (x : nadd) : (term122 y x) = (term122 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1317081 y x z)). Qed.
Lemma lem1317083 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317084 (y : nadd) (x : nadd) : (term123 y x) = (term123 y x).
Proof. exact (MK_COMB (@lem1317083) (@lem1317082 y x)). Qed.
Lemma lem1317085 (x : nadd) : (term124 x) = (term124 x).
Proof. exact (fun_ext (fun y : nadd => @lem1317084 y x)). Qed.
Lemma lem1317086 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317087 (x : nadd) : (term125 x) = (term125 x).
Proof. exact (MK_COMB (@lem1317086) (@lem1317085 x)). Qed.
Lemma lem1317088 : term126 = term126.
Proof. exact (fun_ext (fun x : nadd => @lem1317087 x)). Qed.
Lemma lem1317089 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317091 : term127 = term127.
Proof. exact (MK_COMB (@lem1317089) (@lem1317088)). Qed.
Lemma lem1317092 (h1 : term7) : term127.
Proof. exact (EQ_MP (@lem1317091) (@lem1316942 h1)). Qed.
Lemma lem1317094 (x : nadd) : (term235 x) = (term235 x).
Proof. exact (eq_refl (term235 x)). Qed.
Lemma lem1317095 : term236 = term236.
Proof. exact (fun_ext (fun x : nadd => @lem1317094 x)). Qed.
Lemma lem1317096 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317098 : term237 = term237.
Proof. exact (MK_COMB (@lem1317096) (@lem1317095)). Qed.
Lemma lem1317099 (h1 : term237) : term237.
Proof. exact (EQ_MP (@lem1317098) (@lem1316961 h1)). Qed.
Lemma lem1317101 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1317102 : term300 = term300.
Proof. exact (fun_ext (fun x : nadd => @lem1317101 x)). Qed.
Lemma lem1317103 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317105 : term301 = term301.
Proof. exact (MK_COMB (@lem1317103) (@lem1317102)). Qed.
Lemma lem1317106 (h1 : term301) : term301.
Proof. exact (EQ_MP (@lem1317105) (@lem1316970 h1)). Qed.
Lemma lem1317120 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term308 x y x' y') = (term308 x y x' y').
Proof. exact (eq_refl (term308 x y x' y')). Qed.
Lemma lem1317121 (x : nadd) (y : nadd) (x' : nadd) : (term310 x y x') = (term310 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1317120 x y x' y')). Qed.
Lemma lem1317122 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317123 (x : nadd) (y : nadd) (x' : nadd) : (term311 x y x') = (term311 x y x').
Proof. exact (MK_COMB (@lem1317122) (@lem1317121 x y x')). Qed.
Lemma lem1317124 (x : nadd) (x' : nadd) : (term312 x x') = (term312 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1317123 x y x')). Qed.
Lemma lem1317125 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317126 (x : nadd) (x' : nadd) : (term313 x x') = (term313 x x').
Proof. exact (MK_COMB (@lem1317125) (@lem1317124 x x')). Qed.
Lemma lem1317127 (x : nadd) : (term314 x) = (term314 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1317126 x x')). Qed.
Lemma lem1317128 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317129 (x : nadd) : (term315 x) = (term315 x).
Proof. exact (MK_COMB (@lem1317128) (@lem1317127 x)). Qed.
Lemma lem1317130 : term316 = term316.
Proof. exact (fun_ext (fun x : nadd => @lem1317129 x)). Qed.
Lemma lem1317131 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317133 : term317 = term317.
Proof. exact (MK_COMB (@lem1317131) (@lem1317130)). Qed.
Lemma lem1317134 (h1 : term299) : term317.
Proof. exact (EQ_MP (@lem1317133) (@lem1317016 h1)). Qed.
Lemma lem1317142 (x : nadd) : (term323 x) = (term323 x).
Proof. exact (eq_refl (term323 x)). Qed.
Lemma lem1317143 : term324 = term324.
Proof. exact (fun_ext (fun x : nadd => @lem1317142 x)). Qed.
Lemma lem1317144 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317146 : term325 = term325.
Proof. exact (MK_COMB (@lem1317144) (@lem1317143)). Qed.
Lemma lem1317147 (h1 : term266) : term325.
Proof. exact (EQ_MP (@lem1317146) (@lem1317049 h1)). Qed.
Lemma lem1317171 (y : nadd) (x : nadd) : (term80 y x) = (term80 y x).
Proof. exact (eq_refl (term80 y x)). Qed.
Lemma lem1317172 (x : nadd) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : nadd => @lem1317171 y x)). Qed.
Lemma lem1317173 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317174 (x : nadd) : (term92 x) = (term92 x).
Proof. exact (MK_COMB (@lem1317173) (@lem1317172 x)). Qed.
Lemma lem1317175 : term99 = term99.
Proof. exact (fun_ext (fun x : nadd => @lem1317174 x)). Qed.
Lemma lem1317176 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1317178 : term114 = term114.
Proof. exact (MK_COMB (@lem1317176) (@lem1317175)). Qed.
Lemma lem1317179 (h1 : term61) : term114.
Proof. exact (EQ_MP (@lem1317178) (@lem1317050 h1)). Qed.
Lemma lem1317180 (_23402 : nadd) (h1 : term7) : term128 _23402.
Proof. exact (@lem1317092 h1 _23402). Qed.
Lemma lem1317181 (_23402 : nadd) : (term128 _23402) = (term125 _23402).
Proof. exact (eq_refl (term128 _23402)). Qed.
Lemma lem1317182 (_23402 : nadd) (h1 : term7) : term125 _23402.
Proof. exact (EQ_MP (@lem1317181 _23402) (@lem1317180 _23402 h1)). Qed.
Lemma lem1317183 (_23402 : nadd) (_23403 : nadd) (h1 : term7) : term129 _23402 _23403.
Proof. exact (@lem1317182 _23402 h1 _23403). Qed.
Lemma lem1317184 (_23403 : nadd) (_23402 : nadd) : (term129 _23402 _23403) = (term123 _23403 _23402).
Proof. exact (eq_refl (term129 _23402 _23403)). Qed.
Lemma lem1317185 (_23403 : nadd) (_23402 : nadd) (h1 : term7) : term123 _23403 _23402.
Proof. exact (EQ_MP (@lem1317184 _23403 _23402) (@lem1317183 _23402 _23403 h1)). Qed.
Lemma lem1317186 (_23403 : nadd) (_23402 : nadd) (_23404 : nadd) (h1 : term7) : term130 _23403 _23402 _23404.
Proof. exact (@lem1317185 _23403 _23402 h1 _23404). Qed.
Lemma lem1317187 (_23403 : nadd) (_23402 : nadd) (_23404 : nadd) : (term130 _23403 _23402 _23404) = (term121 _23403 _23402 _23404).
Proof. exact (eq_refl (term130 _23403 _23402 _23404)). Qed.
Lemma lem1317188 (_23403 : nadd) (_23402 : nadd) (_23404 : nadd) (h1 : term7) : term121 _23403 _23402 _23404.
Proof. exact (EQ_MP (@lem1317187 _23403 _23402 _23404) (@lem1317186 _23403 _23402 _23404 h1)). Qed.
Lemma lem1317189 (_23405 : nadd) (h1 : term237) : term238 _23405.
Proof. exact (@lem1317099 h1 _23405). Qed.
Lemma lem1317190 (_23405 : nadd) : (term238 _23405) = (term235 _23405).
Proof. exact (eq_refl (term238 _23405)). Qed.
Lemma lem1317192 (_23406 : nadd) (h1 : term301) : term167 _23406.
Proof. exact (@lem1317106 h1 _23406). Qed.
Lemma lem1317193 (_23406 : nadd) : (term167 _23406) = (nadd_eq _23406 _23406).
Proof. exact (eq_refl (term167 _23406)). Qed.
Lemma lem1317195 (_23407 : nadd) (h1 : term299) : term326 _23407.
Proof. exact (@lem1317134 h1 _23407). Qed.
Lemma lem1317196 (_23407 : nadd) : (term326 _23407) = (term315 _23407).
Proof. exact (eq_refl (term326 _23407)). Qed.
Lemma lem1317197 (_23407 : nadd) (h1 : term299) : term315 _23407.
Proof. exact (EQ_MP (@lem1317196 _23407) (@lem1317195 _23407 h1)). Qed.
Lemma lem1317198 (_23407 : nadd) (_23408 : nadd) (h1 : term299) : term327 _23407 _23408.
Proof. exact (@lem1317197 _23407 h1 _23408). Qed.
Lemma lem1317199 (_23407 : nadd) (_23408 : nadd) : (term327 _23407 _23408) = (term313 _23407 _23408).
Proof. exact (eq_refl (term327 _23407 _23408)). Qed.
Lemma lem1317200 (_23407 : nadd) (_23408 : nadd) (h1 : term299) : term313 _23407 _23408.
Proof. exact (EQ_MP (@lem1317199 _23407 _23408) (@lem1317198 _23407 _23408 h1)). Qed.
Lemma lem1317201 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (h1 : term299) : term328 _23407 _23408 _23409.
Proof. exact (@lem1317200 _23407 _23408 h1 _23409). Qed.
Lemma lem1317202 (_23407 : nadd) (_23409 : nadd) (_23408 : nadd) : (term328 _23407 _23408 _23409) = (term311 _23407 _23409 _23408).
Proof. exact (eq_refl (term328 _23407 _23408 _23409)). Qed.
Lemma lem1317203 (_23407 : nadd) (_23409 : nadd) (_23408 : nadd) (h1 : term299) : term311 _23407 _23409 _23408.
Proof. exact (EQ_MP (@lem1317202 _23407 _23409 _23408) (@lem1317201 _23407 _23408 _23409 h1)). Qed.
Lemma lem1317204 (_23407 : nadd) (_23409 : nadd) (_23408 : nadd) (_23410 : nadd) (h1 : term299) : term329 _23407 _23409 _23408 _23410.
Proof. exact (@lem1317203 _23407 _23409 _23408 h1 _23410). Qed.
Lemma lem1317205 (_23407 : nadd) (_23409 : nadd) (_23408 : nadd) (_23410 : nadd) : (term329 _23407 _23409 _23408 _23410) = (term308 _23407 _23409 _23408 _23410).
Proof. exact (eq_refl (term329 _23407 _23409 _23408 _23410)). Qed.
Lemma lem1317206 (_23407 : nadd) (_23409 : nadd) (_23408 : nadd) (_23410 : nadd) (h1 : term299) : term308 _23407 _23409 _23408 _23410.
Proof. exact (EQ_MP (@lem1317205 _23407 _23409 _23408 _23410) (@lem1317204 _23407 _23409 _23408 _23410 h1)). Qed.
Lemma lem1317207 (_23411 : nadd) (h1 : term266) : term330 _23411.
Proof. exact (@lem1317147 h1 _23411). Qed.
Lemma lem1317208 (_23411 : nadd) : (term330 _23411) = (term323 _23411).
Proof. exact (eq_refl (term330 _23411)). Qed.
Lemma lem1317216 (_23414 : nadd) (h1 : term61) : term102 _23414.
Proof. exact (@lem1317179 h1 _23414). Qed.
Lemma lem1317217 (_23414 : nadd) : (term102 _23414) = (term92 _23414).
Proof. exact (eq_refl (term102 _23414)). Qed.
Lemma lem1317218 (_23414 : nadd) (h1 : term61) : term92 _23414.
Proof. exact (EQ_MP (@lem1317217 _23414) (@lem1317216 _23414 h1)). Qed.
Lemma lem1317219 (_23414 : nadd) (_23415 : nadd) (h1 : term61) : term79 _23414 _23415.
Proof. exact (@lem1317218 _23414 h1 _23415). Qed.
Lemma lem1317220 (_23415 : nadd) (_23414 : nadd) : (term79 _23414 _23415) = (term80 _23415 _23414).
Proof. exact (eq_refl (term79 _23414 _23415)). Qed.
Lemma lem1317227 (y : nadd) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1317229 (y : nadd) (x : nadd) (h1 : term491 y x) : term491 y x.
Proof. exact (h1). Qed.
Lemma lem1317240 (_23403 : nadd) (_23402 : nadd) (_23404 : nadd) : (term121 _23403 _23402 _23404) = (term131 _23403 _23402 _23404).
Proof. exact (@lem1309032 (term132 _23402 _23403) (term132 _23403 _23404) (nadd_eq _23402 _23404)). Qed.
Lemma lem1317241 (_23403 : nadd) (_23402 : nadd) (_23404 : nadd) (h1 : term7) : term131 _23403 _23402 _23404.
Proof. exact (EQ_MP (@lem1317240 _23403 _23402 _23404) (@lem1317188 _23403 _23402 _23404 h1)). Qed.
Lemma lem1317256 (_23407 : nadd) (_23409 : nadd) (_23408 : nadd) (_23410 : nadd) : (term308 _23407 _23409 _23408 _23410) = (term331 _23407 _23409 _23408 _23410).
Proof. exact (@lem1309032 (term132 _23407 _23408) (term132 _23409 _23410) (term304 _23407 _23409 _23408 _23410)). Qed.
Lemma lem1317257 (_23407 : nadd) (_23409 : nadd) (_23408 : nadd) (_23410 : nadd) (h1 : term299) : term331 _23407 _23409 _23408 _23410.
Proof. exact (EQ_MP (@lem1317256 _23407 _23409 _23408 _23410) (@lem1317206 _23407 _23409 _23408 _23410 h1)). Qed.
Lemma lem1317263 (_23411 : nadd) (h1 : term266) : term323 _23411.
Proof. exact (EQ_MP (@lem1317208 _23411) (@lem1317207 _23411 h1)). Qed.
Lemma lem1317275 (_23415 : nadd) (_23414 : nadd) (h1 : term61) : term80 _23415 _23414.
Proof. exact (EQ_MP (@lem1317220 _23415 _23414) (@lem1317219 _23414 _23415 h1)). Qed.
Lemma lem1317277 (y : nadd) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1317278 (y : nadd) (h1 : term27 y) : term335 y.
Proof. exact (fun h0 : term25 y => @lem1317277 y h1). Qed.
Lemma lem1317280 (p : Prop) : (term336 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1317281 (y : nadd) : (term335 y) = (term27 y).
Proof. exact (@lem1317280 (term25 y)). Qed.
Lemma lem1317282 (y : nadd) (h1 : term27 y) : term27 y.
Proof. exact (EQ_MP (@lem1317281 y) (@lem1317278 y h1)). Qed.
Lemma lem1317293 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1317294 (_23411 : nadd) : (term337 _23411) = (term323 _23411).
Proof. exact (@lem1317293 (term25 _23411) (term319 _23411)). Qed.
Lemma lem1317300 (_23411 : nadd) : (term338 _23411) = (term338 _23411).
Proof. exact (eq_refl (term338 _23411)). Qed.
Lemma lem1317301 (_23411 : nadd) : ((term323 _23411) = (term337 _23411)) = ((term323 _23411) = (term323 _23411)).
Proof. exact (MK_COMB (@lem1317300 _23411) (@lem1317294 _23411)). Qed.
Lemma lem1317303 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1317304 (x : Prop) : (x = x) = True.
Proof. exact (@lem1317303 Prop x). Qed.
Lemma lem1317305 (_23411 : nadd) : ((term323 _23411) = (term323 _23411)) = True.
Proof. exact (@lem1317304 (term323 _23411)). Qed.
Lemma lem1317306 (_23411 : nadd) : ((term323 _23411) = (term337 _23411)) = True.
Proof. exact (TRANS (@lem1317301 _23411) (@lem1317305 _23411)). Qed.
Lemma lem1317307 (_23411 : nadd) : True = ((term323 _23411) = (term337 _23411)).
Proof. exact (SYM (@lem1317306 _23411)). Qed.
Lemma lem1317308 (_23411 : nadd) : (term323 _23411) = (term337 _23411).
Proof. exact (EQ_MP (@lem1317307 _23411) (@lem0)). Qed.
Lemma lem1317309 (_23411 : nadd) (h1 : term266) : term337 _23411.
Proof. exact (EQ_MP (@lem1317308 _23411) (@lem1317263 _23411 h1)). Qed.
Lemma lem1317311 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1317314 (_23411 : nadd) : (term337 _23411) = (term289 _23411).
Proof. exact (@lem1317311 (term25 _23411) (term319 _23411)). Qed.
Lemma lem1317317 (_23411 : nadd) (h1 : term266) : term289 _23411.
Proof. exact (EQ_MP (@lem1317314 _23411) (@lem1317309 _23411 h1)). Qed.
Lemma lem1317318 (y : nadd) (h1 : term266) : term289 y.
Proof. exact (@lem1317317 y h1). Qed.
Lemma lem1317321 (y : nadd) (h1 : term266) (h2 : term27 y) : term319 y.
Proof. exact (@lem1317318 y h1 (@lem1317282 y h2)). Qed.
Lemma lem1317322 (y : nadd) (h1 : term266) (h2 : term27 y) : term339 y.
Proof. exact (fun h0 : term340 y => @lem1317321 y h1 h2). Qed.
Lemma lem1317324 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1317325 (y : nadd) : (term339 y) = (term319 y).
Proof. exact (@lem1317324 (term319 y)). Qed.
Lemma lem1317326 (y : nadd) (h1 : term266) (h2 : term27 y) : term319 y.
Proof. exact (EQ_MP (@lem1317325 y) (@lem1317322 y h1 h2)). Qed.
Lemma lem1317328 (_23406 : nadd) (h1 : term301) : nadd_eq _23406 _23406.
Proof. exact (EQ_MP (@lem1317193 _23406) (@lem1317192 _23406 h1)). Qed.
Lemma lem1317329 (x : nadd) (h1 : term301) : term332 x.
Proof. exact (@lem1317328 (nadd_inv x) h1). Qed.
Lemma lem1317330 (x : nadd) (h1 : term301) : term333 x.
Proof. exact (fun h0 : term334 x => @lem1317329 x h1). Qed.
Lemma lem1317332 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1317333 (x : nadd) : (term333 x) = (term332 x).
Proof. exact (@lem1317332 (term332 x)). Qed.
Lemma lem1317334 (x : nadd) (h1 : term301) : term332 x.
Proof. exact (EQ_MP (@lem1317333 x) (@lem1317330 x h1)). Qed.
Lemma lem1317350 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1317351 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : (term341 _23407 _23409 _23408 _23410) = (term342 _23407 _23408 _23409 _23410).
Proof. exact (@lem1317350 (term304 _23407 _23409 _23408 _23410) (term132 _23409 _23410)). Qed.
Lemma lem1317357 (_23407 : nadd) (_23408 : nadd) : (term146 _23407 _23408) = (term146 _23407 _23408).
Proof. exact (eq_refl (term146 _23407 _23408)). Qed.
Lemma lem1317358 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : (term331 _23407 _23409 _23408 _23410) = (term343 _23407 _23408 _23409 _23410).
Proof. exact (MK_COMB (@lem1317357 _23407 _23408) (@lem1317351 _23407 _23408 _23409 _23410)). Qed.
Lemma lem1317362 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1317363 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : (term343 _23407 _23408 _23409 _23410) = (term344 _23407 _23408 _23409 _23410).
Proof. exact (@lem1317362 (term304 _23407 _23409 _23408 _23410) (term132 _23407 _23408) (term132 _23409 _23410)). Qed.
Lemma lem1317379 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : (term331 _23407 _23409 _23408 _23410) = (term344 _23407 _23408 _23409 _23410).
Proof. exact (TRANS (@lem1317358 _23407 _23408 _23409 _23410) (@lem1317363 _23407 _23408 _23409 _23410)). Qed.
Lemma lem1317380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1317381 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : (term345 _23407 _23409 _23408 _23410) = (term346 _23407 _23408 _23409 _23410).
Proof. exact (MK_COMB (@lem1317380) (@lem1317379 _23407 _23408 _23409 _23410)). Qed.
Lemma lem1317397 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : (term344 _23407 _23408 _23409 _23410) = (term344 _23407 _23408 _23409 _23410).
Proof. exact (eq_refl (term344 _23407 _23408 _23409 _23410)). Qed.
Lemma lem1317398 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : ((term331 _23407 _23409 _23408 _23410) = (term344 _23407 _23408 _23409 _23410)) = ((term344 _23407 _23408 _23409 _23410) = (term344 _23407 _23408 _23409 _23410)).
Proof. exact (MK_COMB (@lem1317381 _23407 _23408 _23409 _23410) (@lem1317397 _23407 _23408 _23409 _23410)). Qed.
Lemma lem1317400 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1317401 (x : Prop) : (x = x) = True.
Proof. exact (@lem1317400 Prop x). Qed.
Lemma lem1317402 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : ((term344 _23407 _23408 _23409 _23410) = (term344 _23407 _23408 _23409 _23410)) = True.
Proof. exact (@lem1317401 (term344 _23407 _23408 _23409 _23410)). Qed.
Lemma lem1317403 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : ((term331 _23407 _23409 _23408 _23410) = (term344 _23407 _23408 _23409 _23410)) = True.
Proof. exact (TRANS (@lem1317398 _23407 _23408 _23409 _23410) (@lem1317402 _23407 _23408 _23409 _23410)). Qed.
Lemma lem1317404 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : True = ((term331 _23407 _23409 _23408 _23410) = (term344 _23407 _23408 _23409 _23410)).
Proof. exact (SYM (@lem1317403 _23407 _23408 _23409 _23410)). Qed.
Lemma lem1317405 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : (term331 _23407 _23409 _23408 _23410) = (term344 _23407 _23408 _23409 _23410).
Proof. exact (EQ_MP (@lem1317404 _23407 _23408 _23409 _23410) (@lem0)). Qed.
Lemma lem1317406 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) (h1 : term299) : term344 _23407 _23408 _23409 _23410.
Proof. exact (EQ_MP (@lem1317405 _23407 _23408 _23409 _23410) (@lem1317257 _23407 _23409 _23408 _23410 h1)). Qed.
Lemma lem1317408 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1317409 (_23407 : nadd) (_23409 : nadd) (_23408 : nadd) (_23410 : nadd) : (term344 _23407 _23408 _23409 _23410) = (term347 _23407 _23409 _23408 _23410).
Proof. exact (@lem1317408 (term303 _23407 _23408 _23409 _23410) (term304 _23407 _23409 _23408 _23410)). Qed.
Lemma lem1317411 (a : Prop) (b : Prop) : (term152 a b) = (term153 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1317412 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : (term348 _23407 _23408 _23409 _23410) = (term349 _23407 _23408 _23409 _23410).
Proof. exact (@lem1317411 (term132 _23407 _23408) (term132 _23409 _23410)). Qed.
Lemma lem1317414 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1317415 (_23407 : nadd) (_23408 : nadd) : (term140 _23407 _23408) = (nadd_eq _23407 _23408).
Proof. exact (@lem1317414 (nadd_eq _23407 _23408)). Qed.
Lemma lem1317416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1317417 (_23407 : nadd) (_23408 : nadd) : (term156 _23407 _23408) = (term157 _23407 _23408).
Proof. exact (MK_COMB (@lem1317416) (@lem1317415 _23407 _23408)). Qed.
Lemma lem1317419 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1317420 (_23409 : nadd) (_23410 : nadd) : (term140 _23409 _23410) = (nadd_eq _23409 _23410).
Proof. exact (@lem1317419 (nadd_eq _23409 _23410)). Qed.
Lemma lem1317421 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : (term349 _23407 _23408 _23409 _23410) = (term309 _23407 _23408 _23409 _23410).
Proof. exact (MK_COMB (@lem1317417 _23407 _23408) (@lem1317420 _23409 _23410)). Qed.
Lemma lem1317422 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : (term348 _23407 _23408 _23409 _23410) = (term309 _23407 _23408 _23409 _23410).
Proof. exact (TRANS (@lem1317412 _23407 _23408 _23409 _23410) (@lem1317421 _23407 _23408 _23409 _23410)). Qed.
Lemma lem1317423 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1317424 (_23407 : nadd) (_23408 : nadd) (_23409 : nadd) (_23410 : nadd) : (term350 _23407 _23408 _23409 _23410) = (term351 _23407 _23408 _23409 _23410).
Proof. exact (MK_COMB (@lem1317423) (@lem1317422 _23407 _23408 _23409 _23410)). Qed.
Lemma lem1317425 (_23407 : nadd) (_23409 : nadd) (_23408 : nadd) (_23410 : nadd) : (term304 _23407 _23409 _23408 _23410) = (term304 _23407 _23409 _23408 _23410).
Proof. exact (eq_refl (term304 _23407 _23409 _23408 _23410)). Qed.
Lemma lem1317426 (_23407 : nadd) (_23409 : nadd) (_23408 : nadd) (_23410 : nadd) : (term347 _23407 _23409 _23408 _23410) = (term291 _23407 _23409 _23408 _23410).
Proof. exact (MK_COMB (@lem1317424 _23407 _23408 _23409 _23410) (@lem1317425 _23407 _23409 _23408 _23410)). Qed.
Lemma lem1317427 (_23407 : nadd) (_23409 : nadd) (_23408 : nadd) (_23410 : nadd) : (term344 _23407 _23408 _23409 _23410) = (term291 _23407 _23409 _23408 _23410).
Proof. exact (TRANS (@lem1317409 _23407 _23409 _23408 _23410) (@lem1317426 _23407 _23409 _23408 _23410)). Qed.
Lemma lem1317429 (x : nadd) (y : nadd) (h1 : term266) (h2 : term301) (h3 : term27 y) : term518 y x.
Proof. exact (conj (@lem1317326 y h1 h3) (@lem1317334 x h2)). Qed.
Lemma lem1317431 (_23407 : nadd) (_23409 : nadd) (_23408 : nadd) (_23410 : nadd) (h1 : term299) : term291 _23407 _23409 _23408 _23410.
Proof. exact (EQ_MP (@lem1317427 _23407 _23409 _23408 _23410) (@lem1317406 _23407 _23408 _23409 _23410 h1)). Qed.
Lemma lem1317432 (y : nadd) (x : nadd) (h1 : term299) : term519 y x.
Proof. exact (@lem1317431 (term354 y) (nadd_inv x) term242 (nadd_inv x) h1). Qed.
Lemma lem1317435 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 y) : term520 y x.
Proof. exact (@lem1317432 y x h1 (@lem1317429 x y h2 h3 h4)). Qed.
Lemma lem1317436 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 y) : term521 y x.
Proof. exact (fun h0 : term522 y x => @lem1317435 x y h1 h2 h3 h4). Qed.
Lemma lem1317438 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1317439 (y : nadd) (x : nadd) : (term521 y x) = (term520 y x).
Proof. exact (@lem1317438 (term520 y x)). Qed.
Lemma lem1317440 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term27 y) : term520 y x.
Proof. exact (EQ_MP (@lem1317439 y x) (@lem1317436 x y h1 h2 h3 h4)). Qed.
Lemma lem1317442 (_23405 : nadd) (h1 : term237) : term235 _23405.
Proof. exact (EQ_MP (@lem1317190 _23405) (@lem1317189 _23405 h1)). Qed.
Lemma lem1317443 (x : nadd) (h1 : term237) : term245 x.
Proof. exact (@lem1317442 (nadd_inv x) h1). Qed.
Lemma lem1317444 (x : nadd) (h1 : term237) : term246 x.
Proof. exact (fun h0 : term247 x => @lem1317443 x h1). Qed.
Lemma lem1317446 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1317447 (x : nadd) : (term246 x) = (term245 x).
Proof. exact (@lem1317446 (term245 x)). Qed.
Lemma lem1317448 (x : nadd) (h1 : term237) : term245 x.
Proof. exact (EQ_MP (@lem1317447 x) (@lem1317444 x h1)). Qed.
Lemma lem1317464 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1317465 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : (term144 _23403 _23402 _23404) = (term145 _23402 _23403 _23404).
Proof. exact (@lem1317464 (nadd_eq _23402 _23404) (term132 _23403 _23404)). Qed.
Lemma lem1317471 (_23402 : nadd) (_23403 : nadd) : (term146 _23402 _23403) = (term146 _23402 _23403).
Proof. exact (eq_refl (term146 _23402 _23403)). Qed.
Lemma lem1317472 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : (term131 _23403 _23402 _23404) = (term147 _23402 _23403 _23404).
Proof. exact (MK_COMB (@lem1317471 _23402 _23403) (@lem1317465 _23402 _23403 _23404)). Qed.
Lemma lem1317476 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1317477 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : (term147 _23402 _23403 _23404) = (term148 _23402 _23403 _23404).
Proof. exact (@lem1317476 (nadd_eq _23402 _23404) (term132 _23402 _23403) (term132 _23403 _23404)). Qed.
Lemma lem1317493 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : (term131 _23403 _23402 _23404) = (term148 _23402 _23403 _23404).
Proof. exact (TRANS (@lem1317472 _23402 _23403 _23404) (@lem1317477 _23402 _23403 _23404)). Qed.
Lemma lem1317494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1317495 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : (term149 _23403 _23402 _23404) = (term150 _23402 _23403 _23404).
Proof. exact (MK_COMB (@lem1317494) (@lem1317493 _23402 _23403 _23404)). Qed.
Lemma lem1317511 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : (term148 _23402 _23403 _23404) = (term148 _23402 _23403 _23404).
Proof. exact (eq_refl (term148 _23402 _23403 _23404)). Qed.
Lemma lem1317512 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : ((term131 _23403 _23402 _23404) = (term148 _23402 _23403 _23404)) = ((term148 _23402 _23403 _23404) = (term148 _23402 _23403 _23404)).
Proof. exact (MK_COMB (@lem1317495 _23402 _23403 _23404) (@lem1317511 _23402 _23403 _23404)). Qed.
Lemma lem1317514 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1317515 (x : Prop) : (x = x) = True.
Proof. exact (@lem1317514 Prop x). Qed.
Lemma lem1317516 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : ((term148 _23402 _23403 _23404) = (term148 _23402 _23403 _23404)) = True.
Proof. exact (@lem1317515 (term148 _23402 _23403 _23404)). Qed.
Lemma lem1317517 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : ((term131 _23403 _23402 _23404) = (term148 _23402 _23403 _23404)) = True.
Proof. exact (TRANS (@lem1317512 _23402 _23403 _23404) (@lem1317516 _23402 _23403 _23404)). Qed.
Lemma lem1317518 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : True = ((term131 _23403 _23402 _23404) = (term148 _23402 _23403 _23404)).
Proof. exact (SYM (@lem1317517 _23402 _23403 _23404)). Qed.
Lemma lem1317519 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : (term131 _23403 _23402 _23404) = (term148 _23402 _23403 _23404).
Proof. exact (EQ_MP (@lem1317518 _23402 _23403 _23404) (@lem0)). Qed.
Lemma lem1317520 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) (h1 : term7) : term148 _23402 _23403 _23404.
Proof. exact (EQ_MP (@lem1317519 _23402 _23403 _23404) (@lem1317241 _23403 _23402 _23404 h1)). Qed.
Lemma lem1317522 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1317523 (_23403 : nadd) (_23402 : nadd) (_23404 : nadd) : (term148 _23402 _23403 _23404) = (term151 _23403 _23402 _23404).
Proof. exact (@lem1317522 (term117 _23402 _23403 _23404) (nadd_eq _23402 _23404)). Qed.
Lemma lem1317525 (a : Prop) (b : Prop) : (term152 a b) = (term153 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1317526 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : (term154 _23402 _23403 _23404) = (term155 _23402 _23403 _23404).
Proof. exact (@lem1317525 (term132 _23402 _23403) (term132 _23403 _23404)). Qed.
Lemma lem1317528 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1317529 (_23402 : nadd) (_23403 : nadd) : (term140 _23402 _23403) = (nadd_eq _23402 _23403).
Proof. exact (@lem1317528 (nadd_eq _23402 _23403)). Qed.
Lemma lem1317530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1317531 (_23402 : nadd) (_23403 : nadd) : (term156 _23402 _23403) = (term157 _23402 _23403).
Proof. exact (MK_COMB (@lem1317530) (@lem1317529 _23402 _23403)). Qed.
Lemma lem1317533 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1317534 (_23403 : nadd) (_23404 : nadd) : (term140 _23403 _23404) = (nadd_eq _23403 _23404).
Proof. exact (@lem1317533 (nadd_eq _23403 _23404)). Qed.
Lemma lem1317535 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : (term155 _23402 _23403 _23404) = (term14 _23402 _23403 _23404).
Proof. exact (MK_COMB (@lem1317531 _23402 _23403) (@lem1317534 _23403 _23404)). Qed.
Lemma lem1317536 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : (term154 _23402 _23403 _23404) = (term14 _23402 _23403 _23404).
Proof. exact (TRANS (@lem1317526 _23402 _23403 _23404) (@lem1317535 _23402 _23403 _23404)). Qed.
Lemma lem1317537 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1317538 (_23402 : nadd) (_23403 : nadd) (_23404 : nadd) : (term158 _23402 _23403 _23404) = (term159 _23402 _23403 _23404).
Proof. exact (MK_COMB (@lem1317537) (@lem1317536 _23402 _23403 _23404)). Qed.
Lemma lem1317539 (_23402 : nadd) (_23404 : nadd) : (nadd_eq _23402 _23404) = (nadd_eq _23402 _23404).
Proof. exact (eq_refl (nadd_eq _23402 _23404)). Qed.
Lemma lem1317540 (_23403 : nadd) (_23402 : nadd) (_23404 : nadd) : (term151 _23403 _23402 _23404) = (term13 _23403 _23402 _23404).
Proof. exact (MK_COMB (@lem1317538 _23402 _23403 _23404) (@lem1317539 _23402 _23404)). Qed.
Lemma lem1317541 (_23403 : nadd) (_23402 : nadd) (_23404 : nadd) : (term148 _23402 _23403 _23404) = (term13 _23403 _23402 _23404).
Proof. exact (TRANS (@lem1317523 _23403 _23402 _23404) (@lem1317540 _23403 _23402 _23404)). Qed.
Lemma lem1317543 (x : nadd) (y : nadd) (h1 : term299) (h2 : term266) (h3 : term301) (h4 : term237) (h5 : term27 y) : term523 y x.
Proof. exact (conj (@lem1317440 x y h1 h2 h3 h5) (@lem1317448 x h4)). Qed.
Lemma lem1317545 (_23403 : nadd) (_23402 : nadd) (_23404 : nadd) (h1 : term7) : term13 _23403 _23402 _23404.
Proof. exact (EQ_MP (@lem1317541 _23403 _23402 _23404) (@lem1317520 _23402 _23403 _23404 h1)). Qed.
Lemma lem1317546 (y : nadd) (x : nadd) (h1 : term7) : term524 y x.
Proof. exact (@lem1317545 (term250 x) (term484 y x) (nadd_inv x) h1). Qed.
Lemma lem1317549 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term266) (h4 : term301) (h5 : term237) (h6 : term27 y) : term525 y x.
Proof. exact (@lem1317546 y x h2 (@lem1317543 x y h1 h3 h4 h5 h6)). Qed.
Lemma lem1317550 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term266) (h4 : term301) (h5 : term237) (h6 : term27 y) : term526 y x.
Proof. exact (fun h0 : term527 y x => @lem1317549 x y h1 h2 h3 h4 h5 h6). Qed.
Lemma lem1317552 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1317553 (y : nadd) (x : nadd) : (term526 y x) = (term525 y x).
Proof. exact (@lem1317552 (term525 y x)). Qed.
Lemma lem1317554 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term266) (h4 : term301) (h5 : term237) (h6 : term27 y) : term525 y x.
Proof. exact (EQ_MP (@lem1317553 y x) (@lem1317550 x y h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1317560 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1317561 (_23414 : nadd) (_23415 : nadd) : (term80 _23415 _23414) = (term76 _23414 _23415).
Proof. exact (@lem1317560 (nadd_eq _23415 _23414) (term132 _23414 _23415)). Qed.
Lemma lem1317567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1317568 (_23414 : nadd) (_23415 : nadd) : (term135 _23415 _23414) = (term136 _23414 _23415).
Proof. exact (MK_COMB (@lem1317567) (@lem1317561 _23414 _23415)). Qed.
Lemma lem1317574 (_23414 : nadd) (_23415 : nadd) : (term76 _23414 _23415) = (term76 _23414 _23415).
Proof. exact (eq_refl (term76 _23414 _23415)). Qed.
Lemma lem1317575 (_23414 : nadd) (_23415 : nadd) : ((term80 _23415 _23414) = (term76 _23414 _23415)) = ((term76 _23414 _23415) = (term76 _23414 _23415)).
Proof. exact (MK_COMB (@lem1317568 _23414 _23415) (@lem1317574 _23414 _23415)). Qed.
Lemma lem1317577 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1317578 (x : Prop) : (x = x) = True.
Proof. exact (@lem1317577 Prop x). Qed.
Lemma lem1317579 (_23414 : nadd) (_23415 : nadd) : ((term76 _23414 _23415) = (term76 _23414 _23415)) = True.
Proof. exact (@lem1317578 (term76 _23414 _23415)). Qed.
Lemma lem1317580 (_23414 : nadd) (_23415 : nadd) : ((term80 _23415 _23414) = (term76 _23414 _23415)) = True.
Proof. exact (TRANS (@lem1317575 _23414 _23415) (@lem1317579 _23414 _23415)). Qed.
Lemma lem1317581 (_23414 : nadd) (_23415 : nadd) : True = ((term80 _23415 _23414) = (term76 _23414 _23415)).
Proof. exact (SYM (@lem1317580 _23414 _23415)). Qed.
Lemma lem1317582 (_23414 : nadd) (_23415 : nadd) : (term80 _23415 _23414) = (term76 _23414 _23415).
Proof. exact (EQ_MP (@lem1317581 _23414 _23415) (@lem0)). Qed.
Lemma lem1317583 (_23414 : nadd) (_23415 : nadd) (h1 : term61) : term76 _23414 _23415.
Proof. exact (EQ_MP (@lem1317582 _23414 _23415) (@lem1317275 _23415 _23414 h1)). Qed.
Lemma lem1317585 (b : Prop) (a : Prop) : (a \/ b) = (term137 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1317586 (_23415 : nadd) (_23414 : nadd) : (term76 _23414 _23415) = (term138 _23415 _23414).
Proof. exact (@lem1317585 (term132 _23414 _23415) (nadd_eq _23415 _23414)). Qed.
Lemma lem1317588 (a : Prop) : (term139 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1317589 (_23414 : nadd) (_23415 : nadd) : (term140 _23414 _23415) = (nadd_eq _23414 _23415).
Proof. exact (@lem1317588 (nadd_eq _23414 _23415)). Qed.
Lemma lem1317590 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1317591 (_23414 : nadd) (_23415 : nadd) : (term141 _23414 _23415) = (term45 _23414 _23415).
Proof. exact (MK_COMB (@lem1317590) (@lem1317589 _23414 _23415)). Qed.
Lemma lem1317592 (_23415 : nadd) (_23414 : nadd) : (nadd_eq _23415 _23414) = (nadd_eq _23415 _23414).
Proof. exact (eq_refl (nadd_eq _23415 _23414)). Qed.
Lemma lem1317593 (_23415 : nadd) (_23414 : nadd) : (term138 _23415 _23414) = (term142 _23415 _23414).
Proof. exact (MK_COMB (@lem1317591 _23414 _23415) (@lem1317592 _23415 _23414)). Qed.
Lemma lem1317594 (_23415 : nadd) (_23414 : nadd) : (term76 _23414 _23415) = (term142 _23415 _23414).
Proof. exact (TRANS (@lem1317586 _23415 _23414) (@lem1317593 _23415 _23414)). Qed.
Lemma lem1317597 (_23415 : nadd) (_23414 : nadd) (h1 : term61) : term142 _23415 _23414.
Proof. exact (EQ_MP (@lem1317594 _23415 _23414) (@lem1317583 _23414 _23415 h1)). Qed.
Lemma lem1317598 (y : nadd) (x : nadd) (h1 : term61) : term528 y x.
Proof. exact (@lem1317597 (nadd_inv x) (term484 y x) h1). Qed.
Lemma lem1317601 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) : term489 y x.
Proof. exact (@lem1317598 y x h3 (@lem1317554 x y h1 h2 h4 h5 h6 h7)). Qed.
Lemma lem1317602 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) : term529 y x.
Proof. exact (fun h0 : term491 y x => @lem1317601 x y h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem1317604 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1317605 (y : nadd) (x : nadd) : (term529 y x) = (term489 y x).
Proof. exact (@lem1317604 (term489 y x)). Qed.
Lemma lem1317606 (x : nadd) (y : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) : term489 y x.
Proof. exact (EQ_MP (@lem1317605 y x) (@lem1317602 x y h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem1317609 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1317611 (y : nadd) (x : nadd) : (term491 y x) = (term530 y x).
Proof. exact (@lem1317609 (term489 y x)). Qed.
Lemma lem1317614 (y : nadd) (x : nadd) (h1 : term491 y x) : term530 y x.
Proof. exact (EQ_MP (@lem1317611 y x) (@lem1317229 y x h1)). Qed.
Lemma lem1317617 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (@lem1317614 y x h8 (@lem1317606 x y h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem1317618 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : term164.
Proof. exact (fun h0 : ~ False => @lem1317617 y x h1 h2 h3 h4 h5 h6 h7 h8). Qed.
Lemma lem1317620 (p : Prop) : (term134 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1317621 : term164 = False.
Proof. exact (@lem1317620 False). Qed.
Lemma lem1317622 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317621) (@lem1317618 y x h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem1317623 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : (term491 y x) = False.
Proof. exact (prop_ext (fun h9 : term491 y x => @lem1317622 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1317229 y x h8)). Qed.
Lemma lem1317624 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317623 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1317229 y x h8)). Qed.
Lemma lem1317625 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : (term27 y) = False.
Proof. exact (prop_ext (fun h9 : term27 y => @lem1317624 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1317227 y h7)). Qed.
Lemma lem1317626 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317625 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1317227 y h7)). Qed.
Lemma lem1317627 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : (term491 y x) = False.
Proof. exact (prop_ext (fun h9 : term491 y x => @lem1317626 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1317067 y x h8)). Qed.
Lemma lem1317628 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317627 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1317067 y x h8)). Qed.
Lemma lem1317629 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : (term27 y) = False.
Proof. exact (prop_ext (fun h9 : term27 y => @lem1317628 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1317063 y h7)). Qed.
Lemma lem1317630 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317629 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1317063 y h7)). Qed.
Lemma lem1317631 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : term301 = False.
Proof. exact (prop_ext (fun h9 : term301 => @lem1317630 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1317106 h5)). Qed.
Lemma lem1317632 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317631 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1317106 h5)). Qed.
Lemma lem1317633 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : term237 = False.
Proof. exact (prop_ext (fun h9 : term237 => @lem1317632 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1317099 h6)). Qed.
Lemma lem1317634 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317633 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1317099 h6)). Qed.
Lemma lem1317635 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : (term491 y x) = False.
Proof. exact (prop_ext (fun h9 : term491 y x => @lem1317634 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1317067 y x h8)). Qed.
Lemma lem1317636 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317635 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1317067 y x h8)). Qed.
Lemma lem1317637 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : (term27 y) = False.
Proof. exact (prop_ext (fun h9 : term27 y => @lem1317636 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1317063 y h7)). Qed.
Lemma lem1317638 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317637 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1317063 y h7)). Qed.
Lemma lem1317639 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : term301 = False.
Proof. exact (prop_ext (fun h9 : term301 => @lem1317638 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1316970 h5)). Qed.
Lemma lem1317640 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317639 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1316970 h5)). Qed.
Lemma lem1317641 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : term237 = False.
Proof. exact (prop_ext (fun h9 : term237 => @lem1317640 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1316961 h6)). Qed.
Lemma lem1317642 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317641 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1316961 h6)). Qed.
Lemma lem1317643 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : (term491 y x) = False.
Proof. exact (prop_ext (fun h9 : term491 y x => @lem1317642 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1316861 y x h8)). Qed.
Lemma lem1317644 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317643 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1316861 y x h8)). Qed.
Lemma lem1317645 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : (term27 y) = False.
Proof. exact (prop_ext (fun h9 : term27 y => @lem1317644 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1316839 y h7)). Qed.
Lemma lem1317646 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317645 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1316839 y h7)). Qed.
Lemma lem1317647 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : term301 = False.
Proof. exact (prop_ext (fun h9 : term301 => @lem1317646 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1316654 h5)). Qed.
Lemma lem1317648 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317647 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1316654 h5)). Qed.
Lemma lem1317649 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : term237 = False.
Proof. exact (prop_ext (fun h9 : term237 => @lem1317648 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1316641 h6)). Qed.
Lemma lem1317650 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317649 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1316641 h6)). Qed.
Lemma lem1317651 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : (term491 y x) = False.
Proof. exact (prop_ext (fun h9 : term491 y x => @lem1317650 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1316258 y x h8)). Qed.
Lemma lem1317652 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317651 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1316258 y x h8)). Qed.
Lemma lem1317653 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : (term27 y) = False.
Proof. exact (prop_ext (fun h9 : term27 y => @lem1317652 y x h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1316252 y h7)). Qed.
Lemma lem1317654 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term266) (h5 : term301) (h6 : term237) (h7 : term27 y) (h8 : term491 y x) : False.
Proof. exact (EQ_MP (@lem1317653 y x h1 h2 h3 h4 h5 h6 h7 h8) (@lem1316252 y h7)). Qed.
Lemma lem1317655 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term301) (h5 : term237) (h6 : term27 y) (h7 : term491 y x) : term264.
Proof. exact (fun h0 : term266 => @lem1317654 y x h1 h2 h3 h0 h4 h5 h6 h7). Qed.
Lemma lem1317656 : term264 = term265.
Proof. exact (@lem69 term266). Qed.
Lemma lem1317657 (y : nadd) (x : nadd) (h1 : term299) (h2 : term7) (h3 : term61) (h4 : term301) (h5 : term237) (h6 : term27 y) (h7 : term491 y x) : term265.
Proof. exact (EQ_MP (@lem1317656) (@lem1317655 y x h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem1317658 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term301) (h4 : term237) (h5 : term27 y) (h6 : term491 y x) : term269.
Proof. exact (fun h0 : term299 => @lem1317657 y x h0 h1 h2 h3 h4 h5 h6). Qed.
Lemma lem1317659 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term237) (h4 : term27 y) (h5 : term491 y x) : term272.
Proof. exact (fun h0 : term301 => @lem1317658 y x h1 h2 h0 h3 h4 h5). Qed.
Lemma lem1317660 (y : nadd) (x : nadd) (h1 : term7) (h2 : term61) (h3 : term27 y) (h4 : term491 y x) : term497.
Proof. exact (fun h0 : term237 => @lem1317659 y x h1 h2 h0 h3 h4). Qed.
Lemma lem1317661 (y : nadd) (x : nadd) (h1 : term61) (h2 : term27 y) (h3 : term491 y x) : term499.
Proof. exact (fun h0 : term7 => @lem1317660 y x h0 h1 h2 h3). Qed.
Lemma lem1317662 (y : nadd) (x : nadd) (h1 : term27 y) (h2 : term491 y x) : term501.
Proof. exact (fun h0 : term61 => @lem1317661 y x h0 h1 h2). Qed.
Lemma lem1317663 (x : nadd) (y : nadd) (h1 : term27 y) : term504 y x.
Proof. exact (fun h0 : term491 y x => @lem1317662 y x h1 h0). Qed.
Lemma lem1317664 (y : nadd) (x : nadd) : term506 y x.
Proof. exact (fun h0 : term27 y => @lem1317663 x y h0). Qed.
Lemma lem1317665 (y : nadd) (x : nadd) : term508 y x.
Proof. exact (fun h0 : term27 x => @lem1317664 y x). Qed.
Lemma lem1317666 (y : nadd) (x : nadd) : term509 y x.
Proof. exact (fun h0 : nadd_eq x y => @lem1317665 y x). Qed.
Lemma lem1317671 (x : nadd) : term513 x.
Proof. exact (fun y : nadd => @lem1317666 y x). Qed.
Lemma lem1317676 : term517.
Proof. exact (fun x : nadd => @lem1317671 x). Qed.
Lemma lem1317677 : term516.
Proof. exact (EQ_MP (@lem1316224) (@lem1317676)). Qed.
Lemma lem1317678 (x : nadd) : term531 x.
Proof. exact (@lem1317677 x). Qed.
Lemma lem1317679 (x : nadd) : (term531 x) = (term512 x).
Proof. exact (eq_refl (term531 x)). Qed.
Lemma lem1317680 (x : nadd) : term512 x.
Proof. exact (EQ_MP (@lem1317679 x) (@lem1317678 x)). Qed.
Lemma lem1317681 (x : nadd) (y : nadd) : term532 x y.
Proof. exact (@lem1317680 x y). Qed.
Lemma lem1317682 (y : nadd) (x : nadd) : (term532 x y) = (term492 y x).
Proof. exact (eq_refl (term532 x y)). Qed.
Lemma lem1317683 (y : nadd) (x : nadd) : term492 y x.
Proof. exact (EQ_MP (@lem1317682 y x) (@lem1317681 x y)). Qed.
Lemma lem1317685 (y : nadd) (x : nadd) : term492 y x.
Proof. exact (@lem1315854 y x (@lem1317683 y x)). Qed.
Lemma lem1317686 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term507 y x.
Proof. exact (@lem1317685 y x (@lem1309210 x y h1)). Qed.
Lemma lem1317687 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) : term505 y x.
Proof. exact (@lem1317686 x y h2 (@lem1309209 x h1)). Qed.
Lemma lem1317688 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term503 y x.
Proof. exact (@lem1317687 x y h1 h3 (@lem1310360 y h2)). Qed.
Lemma lem1317689 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term491 y x) (h4 : nadd_eq x y) : term500.
Proof. exact (@lem1317688 x y h1 h2 h4 (@lem1315839 y x h3)). Qed.
Lemma lem1317690 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term491 y x) (h4 : nadd_eq x y) : term498.
Proof. exact (@lem1317689 x y h1 h2 h3 h4 (@lem1268060)). Qed.
Lemma lem1317691 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term491 y x) (h4 : nadd_eq x y) : term496.
Proof. exact (@lem1317690 x y h1 h2 h3 h4 (@lem1268295)). Qed.
Lemma lem1317692 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term491 y x) (h4 : nadd_eq x y) : term271.
Proof. exact (@lem1317691 x y h1 h2 h3 h4 (@lem1278627)). Qed.
Lemma lem1317693 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term491 y x) (h4 : nadd_eq x y) : term268.
Proof. exact (@lem1317692 x y h1 h2 h3 h4 (@lem1267990)). Qed.
Lemma lem1317694 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term491 y x) (h4 : nadd_eq x y) : term264.
Proof. exact (@lem1317693 x y h1 h2 h3 h4 (@lem1279298)). Qed.
Lemma lem1317695 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term491 y x) (h4 : nadd_eq x y) : False.
Proof. exact (@lem1317694 x y h1 h2 h3 h4 (@lem1308984)). Qed.
Lemma lem1317696 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term491 y x) (h4 : nadd_eq x y) : (term491 y x) = False.
Proof. exact (prop_ext (fun h5 : term491 y x => @lem1317695 x y h1 h2 h3 h4) (fun h5 : False => @lem1315839 y x h3)). Qed.
Lemma lem1317697 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : term491 y x) (h4 : nadd_eq x y) : False.
Proof. exact (EQ_MP (@lem1317696 x y h1 h2 h3 h4) (@lem1315839 y x h3)). Qed.
Lemma lem1317698 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term490 y x.
Proof. exact (fun h0 : term491 y x => @lem1317697 x y h1 h2 h0 h3). Qed.
Lemma lem1317699 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term489 y x.
Proof. exact (EQ_MP (@lem1315838 y x) (@lem1317698 x y h1 h2 h3)). Qed.
Lemma lem1317700 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term533 x y.
Proof. exact (conj (@lem1317699 x y h1 h2 h3) (@lem1315834 x y h1 h2 h3)). Qed.
Lemma lem1317701 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term534 x y.
Proof. exact (ex_intro (term535 x y) (term484 y x) (@lem1317700 x y h1 h2 h3)). Qed.
Lemma lem1317702 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term536 x y.
Proof. exact (@lem1314449 x y (@lem1317701 x y h1 h2 h3)). Qed.
Lemma lem1317703 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term537 y x.
Proof. exact (conj (@lem1317702 x y h1 h2 h3) (@lem1314446 x y h1 h2 h3)). Qed.
Lemma lem1317704 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term538 y x.
Proof. exact (ex_intro (term539 y x) (term402 x y) (@lem1317703 x y h1 h2 h3)). Qed.
Lemma lem1317705 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term540 y x.
Proof. exact (@lem1313179 y x (@lem1317704 x y h1 h2 h3)). Qed.
Lemma lem1317706 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term541 x y.
Proof. exact (conj (@lem1317705 x y h1 h2 h3) (@lem1313176 x y h1 h2 h3)). Qed.
Lemma lem1317707 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term542 x y.
Proof. exact (ex_intro (term543 x y) (term360 y x) (@lem1317706 x y h1 h2 h3)). Qed.
Lemma lem1317708 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term544 x y.
Proof. exact (@lem1312215 x y (@lem1317707 x y h1 h2 h3)). Qed.
Lemma lem1317709 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term545 x y.
Proof. exact (conj (@lem1317708 x y h1 h2 h3) (@lem1312212 x y h1 h2 h3)). Qed.
Lemma lem1317710 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term546 x y.
Proof. exact (ex_intro (term547 x y) (term251 y) (@lem1317709 x y h1 h2 h3)). Qed.
Lemma lem1317711 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term177 x y.
Proof. exact (@lem1311394 x y (@lem1317710 x y h1 h2 h3)). Qed.
Lemma lem1317712 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : (term27 y) = (term177 x y).
Proof. exact (prop_ext (fun h4 : term27 y => @lem1317711 x y h1 h2 h3) (fun h4 : term177 x y => @lem1310360 y h2)). Qed.
Lemma lem1317713 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : term27 y) (h3 : nadd_eq x y) : term177 x y.
Proof. exact (EQ_MP (@lem1317712 x y h1 h2 h3) (@lem1310360 y h2)). Qed.
Lemma lem1317714 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) : (term27 y) = (term177 x y).
Proof. exact (prop_ext (fun h3 : term27 y => @lem1317713 x y h1 h3 h2) (fun h3 : term177 x y => @lem1311391 x y h1 h2)). Qed.
Lemma lem1317715 (x : nadd) (y : nadd) (h1 : term27 x) (h2 : nadd_eq x y) : term177 x y.
Proof. exact (EQ_MP (@lem1317714 x y h1 h2) (@lem1311391 x y h1 h2)). Qed.
Lemma lem1317716 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term177 x y.
Proof. exact (or_elim (@lem1309207 x) (fun h0 : term25 x => @lem1310359 y x h1 h0) (fun h0 : term27 x => @lem1317715 x y h0 h1)). Qed.
Lemma lem1317717 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : (nadd_eq x y) = (term177 x y).
Proof. exact (prop_ext (fun h2 : nadd_eq x y => @lem1317716 x y h1) (fun h2 : term177 x y => @lem1309210 x y h1)). Qed.
Lemma lem1317718 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term177 x y.
Proof. exact (EQ_MP (@lem1317717 x y h1) (@lem1309210 x y h1)). Qed.
Lemma lem1317719 (x : nadd) (y : nadd) : term548 x y.
Proof. exact (fun h0 : nadd_eq x y => @lem1317718 x y h0). Qed.
Lemma lem1317724 (x : nadd) : term549 x.
Proof. exact (fun y : nadd => @lem1317719 x y). Qed.
Lemma lem1317729 : term550.
Proof. exact (fun x : nadd => @lem1317724 x). Qed.
