Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import GE_C_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LE_C_spec.
Require Import ge_c_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Lemma lem5128805 {_115054 _115057 : Type'} (s : _115054 -> Prop) : term0 _115054 _115057 s.
Proof. exact (@lem5128794 _115054 _115057 s). Qed.
Lemma lem5128806 {_115054 _115057 : Type'} (s : _115054 -> Prop) : (term0 _115054 _115057 s) = (term1 _115054 _115057 s).
Proof. exact (eq_refl (term0 _115054 _115057 s)). Qed.
Lemma lem5128807 {_115054 _115057 : Type'} (s : _115054 -> Prop) : term1 _115054 _115057 s.
Proof. exact (EQ_MP (@lem5128806 _115054 _115057 s) (@lem5128805 _115054 _115057 s)). Qed.
Lemma lem5128808 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : term2 _115054 _115057 s t.
Proof. exact (@lem5128807 _115054 _115057 s t). Qed.
Lemma lem5128809 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (term2 _115054 _115057 s t) = ((@le_c _115057 _115054 s t) = (term3 _115054 _115057 s t)).
Proof. exact (eq_refl (term2 _115054 _115057 s t)). Qed.
Lemma lem5128811 {_115006 _115007 : Type'} (t : _115006 -> Prop) : term4 _115006 _115007 t.
Proof. exact (@lem5124415 _115006 _115007 t). Qed.
Lemma lem5128812 {_115006 _115007 : Type'} (t : _115006 -> Prop) : (term4 _115006 _115007 t) = (term5 _115006 _115007 t).
Proof. exact (eq_refl (term4 _115006 _115007 t)). Qed.
Lemma lem5128813 {_115006 _115007 : Type'} (t : _115006 -> Prop) : term5 _115006 _115007 t.
Proof. exact (EQ_MP (@lem5128812 _115006 _115007 t) (@lem5128811 _115006 _115007 t)). Qed.
Lemma lem5128814 {_115006 _115007 : Type'} (t : _115006 -> Prop) (s : _115007 -> Prop) : term6 _115006 _115007 t s.
Proof. exact (@lem5128813 _115006 _115007 t s). Qed.
Lemma lem5128815 {_115006 _115007 : Type'} (t : _115006 -> Prop) (s : _115007 -> Prop) : (term6 _115006 _115007 t s) = ((@ge_c _115006 _115007 s t) = (@le_c _115007 _115006 t s)).
Proof. exact (eq_refl (term6 _115006 _115007 t s)). Qed.
Lemma lem5128828 {_115006 _115007 : Type'} (t : _115006 -> Prop) (s : _115007 -> Prop) : (@ge_c _115006 _115007 s t) = (@le_c _115007 _115006 t s).
Proof. exact (EQ_MP (@lem5128815 _115006 _115007 t s) (@lem5128814 _115006 _115007 t s)). Qed.
Lemma lem5128829 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (@ge_c _115095 _115098 s t) = (@le_c _115098 _115095 t s).
Proof. exact (@lem5128828 _115095 _115098 t s). Qed.
Lemma lem5128831 {_115054 _115057 : Type'} (s : _115054 -> Prop) (t : _115057 -> Prop) : (@le_c _115057 _115054 s t) = (term3 _115054 _115057 s t).
Proof. exact (EQ_MP (@lem5128809 _115054 _115057 s t) (@lem5128808 _115054 _115057 s t)). Qed.
Lemma lem5128832 {_115095 _115098 : Type'} (s : _115095 -> Prop) (t : _115098 -> Prop) : (@le_c _115098 _115095 s t) = (term3 _115095 _115098 s t).
Proof. exact (@lem5128831 _115095 _115098 s t). Qed.
Lemma lem5128833 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (@le_c _115098 _115095 t s) = (term3 _115095 _115098 t s).
Proof. exact (@lem5128832 _115095 _115098 t s). Qed.
Lemma lem5128838 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (@ge_c _115095 _115098 s t) = (term3 _115095 _115098 t s).
Proof. exact (TRANS (@lem5128829 _115095 _115098 t s) (@lem5128833 _115095 _115098 t s)). Qed.
Lemma lem5128853 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5128854 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term7 _115095 _115098 s t) = (term8 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5128853) (@lem5128838 _115095 _115098 t s)). Qed.
Lemma lem5128873 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term9 _115095 _115098 t s) = (term9 _115095 _115098 t s).
Proof. exact (eq_refl (term9 _115095 _115098 t s)). Qed.
Lemma lem5128874 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : ((@ge_c _115095 _115098 s t) = (term9 _115095 _115098 t s)) = ((term3 _115095 _115098 t s) = (term9 _115095 _115098 t s)).
Proof. exact (MK_COMB (@lem5128854 _115095 _115098 t s) (@lem5128873 _115095 _115098 t s)). Qed.
Lemma lem5128877 {_115095 _115098 : Type'} (s : _115098 -> Prop) : (term10 _115095 _115098 s) = (term11 _115095 _115098 s).
Proof. exact (fun_ext (fun t : _115095 -> Prop => @lem5128874 _115095 _115098 t s)). Qed.
Lemma lem5128878 {_115095 : Type'} : (@all (_115095 -> Prop)) = (@all (_115095 -> Prop)).
Proof. exact (eq_refl (@all (_115095 -> Prop))). Qed.
Lemma lem5128879 {_115095 _115098 : Type'} (s : _115098 -> Prop) : (term12 _115095 _115098 s) = (term13 _115095 _115098 s).
Proof. exact (MK_COMB (@lem5128878 _115095) (@lem5128877 _115095 _115098 s)). Qed.
Lemma lem5128884 {_115095 _115098 : Type'} : (term14 _115095 _115098) = (term15 _115095 _115098).
Proof. exact (fun_ext (fun s : _115098 -> Prop => @lem5128879 _115095 _115098 s)). Qed.
Lemma lem5128885 {_115098 : Type'} : (@all (_115098 -> Prop)) = (@all (_115098 -> Prop)).
Proof. exact (eq_refl (@all (_115098 -> Prop))). Qed.
Lemma lem5128886 {_115095 _115098 : Type'} : (term16 _115095 _115098) = (term17 _115095 _115098).
Proof. exact (MK_COMB (@lem5128885 _115098) (@lem5128884 _115095 _115098)). Qed.
Lemma lem5128891 {_115095 _115098 : Type'} : (term17 _115095 _115098) = (term16 _115095 _115098).
Proof. exact (SYM (@lem5128886 _115095 _115098)). Qed.
Lemma lem5128893 (p : Prop) : p = (term18 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5128894 {_115095 _115098 : Type'} : (term17 _115095 _115098) = (term19 _115095 _115098).
Proof. exact (@lem5128893 (term17 _115095 _115098)). Qed.
Lemma lem5128895 {_115095 _115098 : Type'} : (term19 _115095 _115098) = (term17 _115095 _115098).
Proof. exact (SYM (@lem5128894 _115095 _115098)). Qed.
Lemma lem5128896 {_115095 _115098 : Type'} (h1 : term20 _115095 _115098) : term20 _115095 _115098.
Proof. exact (h1). Qed.
Lemma lem5128899 {_115095 _115098 : Type'} (h1 : term19 _115095 _115098) : term19 _115095 _115098.
Proof. exact (h1). Qed.
Lemma lem5128900 {_115095 _115098 : Type'} : term21 _115095 _115098.
Proof. exact (fun h0 : term19 _115095 _115098 => @lem5128899 _115095 _115098 h0). Qed.
Lemma lem5128901 {_115095 _115098 : Type'} (h1 : term21 _115095 _115098) : term21 _115095 _115098.
Proof. exact (h1). Qed.
Lemma lem5128902 {_115095 _115098 : Type'} (h1 : term19 _115095 _115098) : term19 _115095 _115098.
Proof. exact (h1). Qed.
Lemma lem5128903 {_115095 _115098 : Type'} (h1 : term19 _115095 _115098) (h2 : term21 _115095 _115098) : term19 _115095 _115098.
Proof. exact (@lem5128901 _115095 _115098 h2 (@lem5128902 _115095 _115098 h1)). Qed.
Lemma lem5128904 {_115095 _115098 : Type'} (h1 : term19 _115095 _115098) : term22 _115095 _115098.
Proof. exact (fun h0 : term21 _115095 _115098 => @lem5128903 _115095 _115098 h1 h0). Qed.
Lemma lem5128905 {_115095 _115098 : Type'} (h1 : term21 _115095 _115098) : term21 _115095 _115098.
Proof. exact (h1). Qed.
Lemma lem5128906 {_115095 _115098 : Type'} (h1 : term19 _115095 _115098) (h2 : term21 _115095 _115098) : term19 _115095 _115098.
Proof. exact (@lem5128904 _115095 _115098 h1 (@lem5128905 _115095 _115098 h2)). Qed.
Lemma lem5128907 {_115095 _115098 : Type'} (h1 : term21 _115095 _115098) : term21 _115095 _115098.
Proof. exact (fun h0 : term19 _115095 _115098 => @lem5128906 _115095 _115098 h0 h1). Qed.
Lemma lem5128908 {_115095 _115098 : Type'} : term23 _115095 _115098.
Proof. exact (fun h0 : term21 _115095 _115098 => @lem5128907 _115095 _115098 h0). Qed.
Lemma lem5128911 {_115095 _115098 : Type'} : term21 _115095 _115098.
Proof. exact (@lem5128908 _115095 _115098 (@lem5128900 _115095 _115098)). Qed.
Lemma lem5128912 {_115095 _115098 : Type'} : term21 _115095 _115098.
Proof. exact (@lem5128911 _115095 _115098). Qed.
Lemma lem5128914 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5128915 {_115095 _115098 : Type'} : (term19 _115095 _115098) = (term24 _115095 _115098).
Proof. exact (@lem5128914 (term20 _115095 _115098)). Qed.
Lemma lem5128917 (t : Prop) : (term25 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5128918 {_115095 _115098 : Type'} : (term24 _115095 _115098) = (term17 _115095 _115098).
Proof. exact (@lem5128917 (term17 _115095 _115098)). Qed.
Lemma lem5129051 {_115095 _115098 : Type'} : (term19 _115095 _115098) = (term17 _115095 _115098).
Proof. exact (TRANS (@lem5128915 _115095 _115098) (@lem5128918 _115095 _115098)). Qed.
Lemma lem5129056 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) (x : _115098) : (term26 _115095 _115098 s y f x) = (term26 _115095 _115098 s y f x).
Proof. exact (eq_refl (term26 _115095 _115098 s y f x)). Qed.
Lemma lem5129057 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term27 _115095 _115098 s y f) = (term27 _115095 _115098 s y f).
Proof. exact (fun_ext (fun x : _115098 => @lem5129056 _115095 _115098 s y f x)). Qed.
Lemma lem5129058 {_115098 : Type'} : (@ex _115098) = (@ex _115098).
Proof. exact (eq_refl (@ex _115098)). Qed.
Lemma lem5129059 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term28 _115095 _115098 s y f) = (term28 _115095 _115098 s y f).
Proof. exact (MK_COMB (@lem5129058 _115098) (@lem5129057 _115095 _115098 s y f)). Qed.
Lemma lem5129062 {_115095 : Type'} (y : _115095) (t : _115095 -> Prop) : (term29 _115095 y t) = (term29 _115095 y t).
Proof. exact (eq_refl (term29 _115095 y t)). Qed.
Lemma lem5129063 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term30 _115095 _115098 t s y f) = (term30 _115095 _115098 t s y f).
Proof. exact (MK_COMB (@lem5129062 _115095 y t) (@lem5129059 _115095 _115098 s y f)). Qed.
Lemma lem5129064 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term31 _115095 _115098 t s f) = (term31 _115095 _115098 t s f).
Proof. exact (fun_ext (fun y : _115095 => @lem5129063 _115095 _115098 t s y f)). Qed.
Lemma lem5129065 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5129066 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term32 _115095 _115098 t s f) = (term32 _115095 _115098 t s f).
Proof. exact (MK_COMB (@lem5129065 _115095) (@lem5129064 _115095 _115098 t s f)). Qed.
Lemma lem5129067 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term33 _115095 _115098 t s) = (term33 _115095 _115098 t s).
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5129066 _115095 _115098 t s f)). Qed.
Lemma lem5129068 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5129069 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term9 _115095 _115098 t s) = (term9 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129068 _115095 _115098) (@lem5129067 _115095 _115098 t s)). Qed.
Lemma lem5129074 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115098) (x : _115095) : (term34 _115095 _115098 s g y x) = (term34 _115095 _115098 s g y x).
Proof. exact (eq_refl (term34 _115095 _115098 s g y x)). Qed.
Lemma lem5129075 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term35 _115095 _115098 s g x) = (term35 _115095 _115098 s g x).
Proof. exact (fun_ext (fun y : _115098 => @lem5129074 _115095 _115098 s g y x)). Qed.
Lemma lem5129076 {_115098 : Type'} : (@ex _115098) = (@ex _115098).
Proof. exact (eq_refl (@ex _115098)). Qed.
Lemma lem5129077 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term36 _115095 _115098 s g x) = (term36 _115095 _115098 s g x).
Proof. exact (MK_COMB (@lem5129076 _115098) (@lem5129075 _115095 _115098 s g x)). Qed.
Lemma lem5129080 {_115095 : Type'} (x : _115095) (t : _115095 -> Prop) : (term29 _115095 x t) = (term29 _115095 x t).
Proof. exact (eq_refl (term29 _115095 x t)). Qed.
Lemma lem5129081 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term37 _115095 _115098 t s g x) = (term37 _115095 _115098 t s g x).
Proof. exact (MK_COMB (@lem5129080 _115095 x t) (@lem5129077 _115095 _115098 s g x)). Qed.
Lemma lem5129082 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term38 _115095 _115098 t s g) = (term38 _115095 _115098 t s g).
Proof. exact (fun_ext (fun x : _115095 => @lem5129081 _115095 _115098 t s g x)). Qed.
Lemma lem5129083 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5129084 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term39 _115095 _115098 t s g) = (term39 _115095 _115098 t s g).
Proof. exact (MK_COMB (@lem5129083 _115095) (@lem5129082 _115095 _115098 t s g)). Qed.
Lemma lem5129085 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term40 _115095 _115098 t s) = (term40 _115095 _115098 t s).
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5129084 _115095 _115098 t s g)). Qed.
Lemma lem5129086 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5129087 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term3 _115095 _115098 t s) = (term3 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129086 _115095 _115098) (@lem5129085 _115095 _115098 t s)). Qed.
Lemma lem5129088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5129089 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term8 _115095 _115098 t s) = (term8 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129088) (@lem5129087 _115095 _115098 t s)). Qed.
Lemma lem5129090 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term3 _115095 _115098 t s) = (term9 _115095 _115098 t s)) = ((term3 _115095 _115098 t s) = (term9 _115095 _115098 t s)).
Proof. exact (MK_COMB (@lem5129089 _115095 _115098 t s) (@lem5129069 _115095 _115098 t s)). Qed.
Lemma lem5129091 {_115095 _115098 : Type'} (s : _115098 -> Prop) : (term11 _115095 _115098 s) = (term11 _115095 _115098 s).
Proof. exact (fun_ext (fun t : _115095 -> Prop => @lem5129090 _115095 _115098 t s)). Qed.
Lemma lem5129092 {_115095 : Type'} : (@all (_115095 -> Prop)) = (@all (_115095 -> Prop)).
Proof. exact (eq_refl (@all (_115095 -> Prop))). Qed.
Lemma lem5129093 {_115095 _115098 : Type'} (s : _115098 -> Prop) : (term13 _115095 _115098 s) = (term13 _115095 _115098 s).
Proof. exact (MK_COMB (@lem5129092 _115095) (@lem5129091 _115095 _115098 s)). Qed.
Lemma lem5129094 {_115095 _115098 : Type'} : (term15 _115095 _115098) = (term15 _115095 _115098).
Proof. exact (fun_ext (fun s : _115098 -> Prop => @lem5129093 _115095 _115098 s)). Qed.
Lemma lem5129095 {_115098 : Type'} : (@all (_115098 -> Prop)) = (@all (_115098 -> Prop)).
Proof. exact (eq_refl (@all (_115098 -> Prop))). Qed.
Lemma lem5129096 {_115095 _115098 : Type'} : (term17 _115095 _115098) = (term17 _115095 _115098).
Proof. exact (MK_COMB (@lem5129095 _115098) (@lem5129094 _115095 _115098)). Qed.
Lemma lem5129155 {_115095 _115098 : Type'} : (term19 _115095 _115098) = (term17 _115095 _115098).
Proof. exact (TRANS (@lem5129051 _115095 _115098) (@lem5129096 _115095 _115098)). Qed.
Lemma lem5129156 {_115095 _115098 : Type'} : (term17 _115095 _115098) = (term19 _115095 _115098).
Proof. exact (SYM (@lem5129155 _115095 _115098)). Qed.
Lemma lem5129158 (p : Prop) : p = (term18 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5129159 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term3 _115095 _115098 t s) = (term9 _115095 _115098 t s)) = (term41 _115095 _115098 t s).
Proof. exact (@lem5129158 ((term3 _115095 _115098 t s) = (term9 _115095 _115098 t s))). Qed.
Lemma lem5129160 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term41 _115095 _115098 t s) = ((term3 _115095 _115098 t s) = (term9 _115095 _115098 t s)).
Proof. exact (SYM (@lem5129159 _115095 _115098 t s)). Qed.
Lemma lem5129161 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (h1 : term42 _115095 _115098 t s) : term42 _115095 _115098 t s.
Proof. exact (h1). Qed.
Lemma lem5129172 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115098) (x : _115095) : (term43 _115095 _115098 s g y x) = (term44 _115095 _115098 s g y x).
Proof. exact (@lem17045 (@IN _115098 y s) ((g y) = x)). Qed.
Lemma lem5129175 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115098) (x : _115095) : (term34 _115095 _115098 s g y x) = (term34 _115095 _115098 s g y x).
Proof. exact (eq_refl (term34 _115095 _115098 s g y x)). Qed.
Lemma lem5129176 {_115098 : Type'} (P : _115098 -> Prop) : (term45 _115098 P) = (term46 _115098 P).
Proof. exact (@lem18394 _115098 P). Qed.
Lemma lem5129177 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term47 _115095 _115098 s g x) = (term48 _115095 _115098 s g x).
Proof. exact (@lem5129176 _115098 (term35 _115095 _115098 s g x)). Qed.
Lemma lem5129178 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115098) (x : _115095) : (term49 _115095 _115098 s g x y) = (term34 _115095 _115098 s g y x).
Proof. exact (eq_refl (term49 _115095 _115098 s g x y)). Qed.
Lemma lem5129179 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5129180 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115098) (x : _115095) : (term50 _115095 _115098 s g x y) = (term43 _115095 _115098 s g y x).
Proof. exact (MK_COMB (@lem5129179) (@lem5129178 _115095 _115098 s g y x)). Qed.
Lemma lem5129181 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115098) (x : _115095) : (term50 _115095 _115098 s g x y) = (term44 _115095 _115098 s g y x).
Proof. exact (TRANS (@lem5129180 _115095 _115098 s g y x) (@lem5129172 _115095 _115098 s g y x)). Qed.
Lemma lem5129182 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term51 _115095 _115098 s g x) = (term52 _115095 _115098 s g x).
Proof. exact (fun_ext (fun y : _115098 => @lem5129181 _115095 _115098 s g y x)). Qed.
Lemma lem5129183 {_115098 : Type'} : (@all _115098) = (@all _115098).
Proof. exact (eq_refl (@all _115098)). Qed.
Lemma lem5129184 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term48 _115095 _115098 s g x) = (term53 _115095 _115098 s g x).
Proof. exact (MK_COMB (@lem5129183 _115098) (@lem5129182 _115095 _115098 s g x)). Qed.
Lemma lem5129185 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term47 _115095 _115098 s g x) = (term53 _115095 _115098 s g x).
Proof. exact (TRANS (@lem5129177 _115095 _115098 s g x) (@lem5129184 _115095 _115098 s g x)). Qed.
Lemma lem5129186 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term35 _115095 _115098 s g x) = (term35 _115095 _115098 s g x).
Proof. exact (fun_ext (fun y : _115098 => @lem5129175 _115095 _115098 s g y x)). Qed.
Lemma lem5129187 {_115098 : Type'} : (@ex _115098) = (@ex _115098).
Proof. exact (eq_refl (@ex _115098)). Qed.
Lemma lem5129188 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term36 _115095 _115098 s g x) = (term36 _115095 _115098 s g x).
Proof. exact (MK_COMB (@lem5129187 _115098) (@lem5129186 _115095 _115098 s g x)). Qed.
Lemma lem5129190 {_115095 : Type'} (x : _115095) (t : _115095 -> Prop) : (term54 _115095 x t) = (term54 _115095 x t).
Proof. exact (eq_refl (term54 _115095 x t)). Qed.
Lemma lem5129191 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term55 _115095 _115098 t s g x) = (term56 _115095 _115098 t s g x).
Proof. exact (MK_COMB (@lem5129190 _115095 x t) (@lem5129185 _115095 _115098 s g x)). Qed.
Lemma lem5129192 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term57 _115095 _115098 t s g x) = (term55 _115095 _115098 t s g x).
Proof. exact (@lem17362 (@IN _115095 x t) (term36 _115095 _115098 s g x)). Qed.
Lemma lem5129193 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term57 _115095 _115098 t s g x) = (term56 _115095 _115098 t s g x).
Proof. exact (TRANS (@lem5129192 _115095 _115098 t s g x) (@lem5129191 _115095 _115098 t s g x)). Qed.
Lemma lem5129195 {_115095 : Type'} (x : _115095) (t : _115095 -> Prop) : (term58 _115095 x t) = (term58 _115095 x t).
Proof. exact (eq_refl (term58 _115095 x t)). Qed.
Lemma lem5129196 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term59 _115095 _115098 t s g x) = (term59 _115095 _115098 t s g x).
Proof. exact (MK_COMB (@lem5129195 _115095 x t) (@lem5129188 _115095 _115098 s g x)). Qed.
Lemma lem5129197 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term37 _115095 _115098 t s g x) = (term59 _115095 _115098 t s g x).
Proof. exact (@lem17265 (@IN _115095 x t) (term36 _115095 _115098 s g x)). Qed.
Lemma lem5129198 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term37 _115095 _115098 t s g x) = (term59 _115095 _115098 t s g x).
Proof. exact (TRANS (@lem5129197 _115095 _115098 t s g x) (@lem5129196 _115095 _115098 t s g x)). Qed.
Lemma lem5129199 {_115095 : Type'} (P : _115095 -> Prop) : (term60 _115095 P) = (term61 _115095 P).
Proof. exact (@lem18392 _115095 P). Qed.
Lemma lem5129200 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term62 _115095 _115098 t s g) = (term63 _115095 _115098 t s g).
Proof. exact (@lem5129199 _115095 (term38 _115095 _115098 t s g)). Qed.
Lemma lem5129201 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term64 _115095 _115098 t s g x) = (term37 _115095 _115098 t s g x).
Proof. exact (eq_refl (term64 _115095 _115098 t s g x)). Qed.
Lemma lem5129202 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5129203 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term65 _115095 _115098 t s g x) = (term57 _115095 _115098 t s g x).
Proof. exact (MK_COMB (@lem5129202) (@lem5129201 _115095 _115098 t s g x)). Qed.
Lemma lem5129204 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term65 _115095 _115098 t s g x) = (term56 _115095 _115098 t s g x).
Proof. exact (TRANS (@lem5129203 _115095 _115098 t s g x) (@lem5129193 _115095 _115098 t s g x)). Qed.
Lemma lem5129205 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term66 _115095 _115098 t s g) = (term67 _115095 _115098 t s g).
Proof. exact (fun_ext (fun x : _115095 => @lem5129204 _115095 _115098 t s g x)). Qed.
Lemma lem5129206 {_115095 : Type'} : (@ex _115095) = (@ex _115095).
Proof. exact (eq_refl (@ex _115095)). Qed.
Lemma lem5129207 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term63 _115095 _115098 t s g) = (term68 _115095 _115098 t s g).
Proof. exact (MK_COMB (@lem5129206 _115095) (@lem5129205 _115095 _115098 t s g)). Qed.
Lemma lem5129208 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term62 _115095 _115098 t s g) = (term68 _115095 _115098 t s g).
Proof. exact (TRANS (@lem5129200 _115095 _115098 t s g) (@lem5129207 _115095 _115098 t s g)). Qed.
Lemma lem5129209 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term38 _115095 _115098 t s g) = (term69 _115095 _115098 t s g).
Proof. exact (fun_ext (fun x : _115095 => @lem5129198 _115095 _115098 t s g x)). Qed.
Lemma lem5129210 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5129211 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term39 _115095 _115098 t s g) = (term70 _115095 _115098 t s g).
Proof. exact (MK_COMB (@lem5129210 _115095) (@lem5129209 _115095 _115098 t s g)). Qed.
Lemma lem5129212 {_115095 _115098 : Type'} (P : type805 _115095 _115098) : (term71 _115095 _115098 P) = (term72 _115095 _115098 P).
Proof. exact (@lem18394 (_115098 -> _115095) P). Qed.
Lemma lem5129213 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term73 _115095 _115098 t s) = (term74 _115095 _115098 t s).
Proof. exact (@lem5129212 _115095 _115098 (term40 _115095 _115098 t s)). Qed.
Lemma lem5129214 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term75 _115095 _115098 t s g) = (term39 _115095 _115098 t s g).
Proof. exact (eq_refl (term75 _115095 _115098 t s g)). Qed.
Lemma lem5129215 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5129216 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term76 _115095 _115098 t s g) = (term62 _115095 _115098 t s g).
Proof. exact (MK_COMB (@lem5129215) (@lem5129214 _115095 _115098 t s g)). Qed.
Lemma lem5129217 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term76 _115095 _115098 t s g) = (term68 _115095 _115098 t s g).
Proof. exact (TRANS (@lem5129216 _115095 _115098 t s g) (@lem5129208 _115095 _115098 t s g)). Qed.
Lemma lem5129218 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term77 _115095 _115098 t s) = (term78 _115095 _115098 t s).
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5129217 _115095 _115098 t s g)). Qed.
Lemma lem5129219 {_115095 _115098 : Type'} : (@all (_115098 -> _115095)) = (@all (_115098 -> _115095)).
Proof. exact (eq_refl (@all (_115098 -> _115095))). Qed.
Lemma lem5129220 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term74 _115095 _115098 t s) = (term79 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129219 _115095 _115098) (@lem5129218 _115095 _115098 t s)). Qed.
Lemma lem5129221 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term73 _115095 _115098 t s) = (term79 _115095 _115098 t s).
Proof. exact (TRANS (@lem5129213 _115095 _115098 t s) (@lem5129220 _115095 _115098 t s)). Qed.
Lemma lem5129222 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term40 _115095 _115098 t s) = (term80 _115095 _115098 t s).
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5129211 _115095 _115098 t s g)). Qed.
Lemma lem5129223 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5129224 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term3 _115095 _115098 t s) = (term81 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129223 _115095 _115098) (@lem5129222 _115095 _115098 t s)). Qed.
Lemma lem5129235 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) (x : _115098) : (term82 _115095 _115098 s y f x) = (term83 _115095 _115098 s y f x).
Proof. exact (@lem17045 (@IN _115098 x s) (y = (f x))). Qed.
Lemma lem5129238 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) (x : _115098) : (term26 _115095 _115098 s y f x) = (term26 _115095 _115098 s y f x).
Proof. exact (eq_refl (term26 _115095 _115098 s y f x)). Qed.
Lemma lem5129239 {_115098 : Type'} (P : _115098 -> Prop) : (term45 _115098 P) = (term46 _115098 P).
Proof. exact (@lem18394 _115098 P). Qed.
Lemma lem5129240 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term84 _115095 _115098 s y f) = (term85 _115095 _115098 s y f).
Proof. exact (@lem5129239 _115098 (term27 _115095 _115098 s y f)). Qed.
Lemma lem5129241 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) (x : _115098) : (term86 _115095 _115098 s y f x) = (term26 _115095 _115098 s y f x).
Proof. exact (eq_refl (term86 _115095 _115098 s y f x)). Qed.
Lemma lem5129242 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5129243 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) (x : _115098) : (term87 _115095 _115098 s y f x) = (term82 _115095 _115098 s y f x).
Proof. exact (MK_COMB (@lem5129242) (@lem5129241 _115095 _115098 s y f x)). Qed.
Lemma lem5129244 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) (x : _115098) : (term87 _115095 _115098 s y f x) = (term83 _115095 _115098 s y f x).
Proof. exact (TRANS (@lem5129243 _115095 _115098 s y f x) (@lem5129235 _115095 _115098 s y f x)). Qed.
Lemma lem5129245 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term88 _115095 _115098 s y f) = (term89 _115095 _115098 s y f).
Proof. exact (fun_ext (fun x : _115098 => @lem5129244 _115095 _115098 s y f x)). Qed.
Lemma lem5129246 {_115098 : Type'} : (@all _115098) = (@all _115098).
Proof. exact (eq_refl (@all _115098)). Qed.
Lemma lem5129247 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term85 _115095 _115098 s y f) = (term90 _115095 _115098 s y f).
Proof. exact (MK_COMB (@lem5129246 _115098) (@lem5129245 _115095 _115098 s y f)). Qed.
Lemma lem5129248 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term84 _115095 _115098 s y f) = (term90 _115095 _115098 s y f).
Proof. exact (TRANS (@lem5129240 _115095 _115098 s y f) (@lem5129247 _115095 _115098 s y f)). Qed.
Lemma lem5129249 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term27 _115095 _115098 s y f) = (term27 _115095 _115098 s y f).
Proof. exact (fun_ext (fun x : _115098 => @lem5129238 _115095 _115098 s y f x)). Qed.
Lemma lem5129250 {_115098 : Type'} : (@ex _115098) = (@ex _115098).
Proof. exact (eq_refl (@ex _115098)). Qed.
Lemma lem5129251 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term28 _115095 _115098 s y f) = (term28 _115095 _115098 s y f).
Proof. exact (MK_COMB (@lem5129250 _115098) (@lem5129249 _115095 _115098 s y f)). Qed.
Lemma lem5129253 {_115095 : Type'} (y : _115095) (t : _115095 -> Prop) : (term54 _115095 y t) = (term54 _115095 y t).
Proof. exact (eq_refl (term54 _115095 y t)). Qed.
Lemma lem5129254 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term91 _115095 _115098 t s y f) = (term92 _115095 _115098 t s y f).
Proof. exact (MK_COMB (@lem5129253 _115095 y t) (@lem5129248 _115095 _115098 s y f)). Qed.
Lemma lem5129255 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term93 _115095 _115098 t s y f) = (term91 _115095 _115098 t s y f).
Proof. exact (@lem17362 (@IN _115095 y t) (term28 _115095 _115098 s y f)). Qed.
Lemma lem5129256 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term93 _115095 _115098 t s y f) = (term92 _115095 _115098 t s y f).
Proof. exact (TRANS (@lem5129255 _115095 _115098 t s y f) (@lem5129254 _115095 _115098 t s y f)). Qed.
Lemma lem5129258 {_115095 : Type'} (y : _115095) (t : _115095 -> Prop) : (term58 _115095 y t) = (term58 _115095 y t).
Proof. exact (eq_refl (term58 _115095 y t)). Qed.
Lemma lem5129259 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term94 _115095 _115098 t s y f) = (term94 _115095 _115098 t s y f).
Proof. exact (MK_COMB (@lem5129258 _115095 y t) (@lem5129251 _115095 _115098 s y f)). Qed.
Lemma lem5129260 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term30 _115095 _115098 t s y f) = (term94 _115095 _115098 t s y f).
Proof. exact (@lem17265 (@IN _115095 y t) (term28 _115095 _115098 s y f)). Qed.
Lemma lem5129261 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term30 _115095 _115098 t s y f) = (term94 _115095 _115098 t s y f).
Proof. exact (TRANS (@lem5129260 _115095 _115098 t s y f) (@lem5129259 _115095 _115098 t s y f)). Qed.
Lemma lem5129262 {_115095 : Type'} (P : _115095 -> Prop) : (term60 _115095 P) = (term61 _115095 P).
Proof. exact (@lem18392 _115095 P). Qed.
Lemma lem5129263 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term95 _115095 _115098 t s f) = (term96 _115095 _115098 t s f).
Proof. exact (@lem5129262 _115095 (term31 _115095 _115098 t s f)). Qed.
Lemma lem5129264 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term97 _115095 _115098 t s f y) = (term30 _115095 _115098 t s y f).
Proof. exact (eq_refl (term97 _115095 _115098 t s f y)). Qed.
Lemma lem5129265 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5129266 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term98 _115095 _115098 t s f y) = (term93 _115095 _115098 t s y f).
Proof. exact (MK_COMB (@lem5129265) (@lem5129264 _115095 _115098 t s y f)). Qed.
Lemma lem5129267 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term98 _115095 _115098 t s f y) = (term92 _115095 _115098 t s y f).
Proof. exact (TRANS (@lem5129266 _115095 _115098 t s y f) (@lem5129256 _115095 _115098 t s y f)). Qed.
Lemma lem5129268 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term99 _115095 _115098 t s f) = (term100 _115095 _115098 t s f).
Proof. exact (fun_ext (fun y : _115095 => @lem5129267 _115095 _115098 t s y f)). Qed.
Lemma lem5129269 {_115095 : Type'} : (@ex _115095) = (@ex _115095).
Proof. exact (eq_refl (@ex _115095)). Qed.
Lemma lem5129270 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term96 _115095 _115098 t s f) = (term101 _115095 _115098 t s f).
Proof. exact (MK_COMB (@lem5129269 _115095) (@lem5129268 _115095 _115098 t s f)). Qed.
Lemma lem5129271 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term95 _115095 _115098 t s f) = (term101 _115095 _115098 t s f).
Proof. exact (TRANS (@lem5129263 _115095 _115098 t s f) (@lem5129270 _115095 _115098 t s f)). Qed.
Lemma lem5129272 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term31 _115095 _115098 t s f) = (term102 _115095 _115098 t s f).
Proof. exact (fun_ext (fun y : _115095 => @lem5129261 _115095 _115098 t s y f)). Qed.
Lemma lem5129273 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5129274 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term32 _115095 _115098 t s f) = (term103 _115095 _115098 t s f).
Proof. exact (MK_COMB (@lem5129273 _115095) (@lem5129272 _115095 _115098 t s f)). Qed.
Lemma lem5129275 {_115095 _115098 : Type'} (P : type805 _115095 _115098) : (term71 _115095 _115098 P) = (term72 _115095 _115098 P).
Proof. exact (@lem18394 (_115098 -> _115095) P). Qed.
Lemma lem5129276 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term104 _115095 _115098 t s) = (term105 _115095 _115098 t s).
Proof. exact (@lem5129275 _115095 _115098 (term33 _115095 _115098 t s)). Qed.
Lemma lem5129277 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term106 _115095 _115098 t s f) = (term32 _115095 _115098 t s f).
Proof. exact (eq_refl (term106 _115095 _115098 t s f)). Qed.
Lemma lem5129278 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5129279 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term107 _115095 _115098 t s f) = (term95 _115095 _115098 t s f).
Proof. exact (MK_COMB (@lem5129278) (@lem5129277 _115095 _115098 t s f)). Qed.
Lemma lem5129280 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term107 _115095 _115098 t s f) = (term101 _115095 _115098 t s f).
Proof. exact (TRANS (@lem5129279 _115095 _115098 t s f) (@lem5129271 _115095 _115098 t s f)). Qed.
Lemma lem5129281 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term108 _115095 _115098 t s) = (term109 _115095 _115098 t s).
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5129280 _115095 _115098 t s f)). Qed.
Lemma lem5129282 {_115095 _115098 : Type'} : (@all (_115098 -> _115095)) = (@all (_115098 -> _115095)).
Proof. exact (eq_refl (@all (_115098 -> _115095))). Qed.
Lemma lem5129283 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term105 _115095 _115098 t s) = (term110 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129282 _115095 _115098) (@lem5129281 _115095 _115098 t s)). Qed.
Lemma lem5129284 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term104 _115095 _115098 t s) = (term110 _115095 _115098 t s).
Proof. exact (TRANS (@lem5129276 _115095 _115098 t s) (@lem5129283 _115095 _115098 t s)). Qed.
Lemma lem5129285 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term33 _115095 _115098 t s) = (term111 _115095 _115098 t s).
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5129274 _115095 _115098 t s f)). Qed.
Lemma lem5129286 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5129287 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term9 _115095 _115098 t s) = (term112 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129286 _115095 _115098) (@lem5129285 _115095 _115098 t s)). Qed.
Lemma lem5129288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5129289 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term113 _115095 _115098 t s) = (term114 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129288) (@lem5129221 _115095 _115098 t s)). Qed.
Lemma lem5129290 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term115 _115095 _115098 t s) = (term116 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129289 _115095 _115098 t s) (@lem5129287 _115095 _115098 t s)). Qed.
Lemma lem5129291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5129292 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term117 _115095 _115098 t s) = (term118 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129291) (@lem5129224 _115095 _115098 t s)). Qed.
Lemma lem5129293 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term119 _115095 _115098 t s) = (term120 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129292 _115095 _115098 t s) (@lem5129284 _115095 _115098 t s)). Qed.
Lemma lem5129294 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5129295 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term121 _115095 _115098 t s) = (term122 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129294) (@lem5129293 _115095 _115098 t s)). Qed.
Lemma lem5129296 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term123 _115095 _115098 t s) = (term124 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129295 _115095 _115098 t s) (@lem5129290 _115095 _115098 t s)). Qed.
Lemma lem5129297 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term42 _115095 _115098 t s) = (term123 _115095 _115098 t s).
Proof. exact (@lem17646 (term3 _115095 _115098 t s) (term9 _115095 _115098 t s)). Qed.
Lemma lem5129298 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term42 _115095 _115098 t s) = (term124 _115095 _115098 t s).
Proof. exact (TRANS (@lem5129297 _115095 _115098 t s) (@lem5129296 _115095 _115098 t s)). Qed.
Lemma lem5129701 {A : Type'} (P : Prop) (Q : A -> Prop) : (term125 A P Q) = (term126 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5129702 {_115098 : Type'} (P : Prop) (Q : _115098 -> Prop) : (term125 _115098 P Q) = (term126 _115098 P Q).
Proof. exact (@lem5129701 _115098 P Q). Qed.
Lemma lem5129703 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term127 _115095 _115098 t s g x) = (term128 _115095 _115098 t s g x).
Proof. exact (@lem5129702 _115098 (term129 _115095 x t) (term35 _115095 _115098 s g x)). Qed.
Lemma lem5129704 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115098) (x : _115095) : (term49 _115095 _115098 s g x y) = (term34 _115095 _115098 s g y x).
Proof. exact (eq_refl (term49 _115095 _115098 s g x y)). Qed.
Lemma lem5129705 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term130 _115095 _115098 s g x) = (term35 _115095 _115098 s g x).
Proof. exact (fun_ext (fun y : _115098 => @lem5129704 _115095 _115098 s g y x)). Qed.
Lemma lem5129706 {_115098 : Type'} : (@ex _115098) = (@ex _115098).
Proof. exact (eq_refl (@ex _115098)). Qed.
Lemma lem5129707 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term131 _115095 _115098 s g x) = (term36 _115095 _115098 s g x).
Proof. exact (MK_COMB (@lem5129706 _115098) (@lem5129705 _115095 _115098 s g x)). Qed.
Lemma lem5129708 {_115095 : Type'} (x : _115095) (t : _115095 -> Prop) : (term58 _115095 x t) = (term58 _115095 x t).
Proof. exact (eq_refl (term58 _115095 x t)). Qed.
Lemma lem5129709 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term127 _115095 _115098 t s g x) = (term59 _115095 _115098 t s g x).
Proof. exact (MK_COMB (@lem5129708 _115095 x t) (@lem5129707 _115095 _115098 s g x)). Qed.
Lemma lem5129710 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5129711 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term132 _115095 _115098 t s g x) = (term133 _115095 _115098 t s g x).
Proof. exact (MK_COMB (@lem5129710) (@lem5129709 _115095 _115098 t s g x)). Qed.
Lemma lem5129712 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115098) (x : _115095) : (term49 _115095 _115098 s g x y) = (term34 _115095 _115098 s g y x).
Proof. exact (eq_refl (term49 _115095 _115098 s g x y)). Qed.
Lemma lem5129713 {_115095 : Type'} (x : _115095) (t : _115095 -> Prop) : (term58 _115095 x t) = (term58 _115095 x t).
Proof. exact (eq_refl (term58 _115095 x t)). Qed.
Lemma lem5129714 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115098) (x : _115095) : (term134 _115095 _115098 t s g x y) = (term135 _115095 _115098 t s g y x).
Proof. exact (MK_COMB (@lem5129713 _115095 x t) (@lem5129712 _115095 _115098 s g y x)). Qed.
Lemma lem5129715 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term136 _115095 _115098 t s g x) = (term137 _115095 _115098 t s g x).
Proof. exact (fun_ext (fun y : _115098 => @lem5129714 _115095 _115098 t s g y x)). Qed.
Lemma lem5129716 {_115098 : Type'} : (@ex _115098) = (@ex _115098).
Proof. exact (eq_refl (@ex _115098)). Qed.
Lemma lem5129717 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term128 _115095 _115098 t s g x) = (term138 _115095 _115098 t s g x).
Proof. exact (MK_COMB (@lem5129716 _115098) (@lem5129715 _115095 _115098 t s g x)). Qed.
Lemma lem5129718 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : ((term127 _115095 _115098 t s g x) = (term128 _115095 _115098 t s g x)) = ((term59 _115095 _115098 t s g x) = (term138 _115095 _115098 t s g x)).
Proof. exact (MK_COMB (@lem5129711 _115095 _115098 t s g x) (@lem5129717 _115095 _115098 t s g x)). Qed.
Lemma lem5129719 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term59 _115095 _115098 t s g x) = (term138 _115095 _115098 t s g x).
Proof. exact (EQ_MP (@lem5129718 _115095 _115098 t s g x) (@lem5129703 _115095 _115098 t s g x)). Qed.
Lemma lem5129720 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term69 _115095 _115098 t s g) = (term139 _115095 _115098 t s g).
Proof. exact (fun_ext (fun x : _115095 => @lem5129719 _115095 _115098 t s g x)). Qed.
Lemma lem5129721 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5129722 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term70 _115095 _115098 t s g) = (term140 _115095 _115098 t s g).
Proof. exact (MK_COMB (@lem5129721 _115095) (@lem5129720 _115095 _115098 t s g)). Qed.
Lemma lem5129724 {A B : Type'} (P : type1413 A B) : (term141 A B P) = (term142 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5129725 {_115095 _115098 : Type'} (P : type1413 _115095 _115098) : (term141 _115095 _115098 P) = (term142 _115095 _115098 P).
Proof. exact (@lem5129724 _115095 _115098 P). Qed.
Lemma lem5129726 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term143 _115095 _115098 t s g) = (term144 _115095 _115098 t s g).
Proof. exact (@lem5129725 _115095 _115098 (term145 _115095 _115098 t s g)). Qed.
Lemma lem5129727 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term146 _115095 _115098 t s g x) = (term137 _115095 _115098 t s g x).
Proof. exact (eq_refl (term146 _115095 _115098 t s g x)). Qed.
Lemma lem5129728 {_115098 : Type'} (y : _115098) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5129729 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) (y : _115098) : (term147 _115095 _115098 t s g x y) = (term148 _115095 _115098 t s g x y).
Proof. exact (MK_COMB (@lem5129727 _115095 _115098 t s g x) (@lem5129728 _115098 y)). Qed.
Lemma lem5129730 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115098) (x : _115095) : (term148 _115095 _115098 t s g x y) = (term135 _115095 _115098 t s g y x).
Proof. exact (eq_refl (term148 _115095 _115098 t s g x y)). Qed.
Lemma lem5129731 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115098) (x : _115095) : (term147 _115095 _115098 t s g x y) = (term135 _115095 _115098 t s g y x).
Proof. exact (TRANS (@lem5129729 _115095 _115098 t s g x y) (@lem5129730 _115095 _115098 t s g y x)). Qed.
Lemma lem5129732 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term149 _115095 _115098 t s g x) = (term137 _115095 _115098 t s g x).
Proof. exact (fun_ext (fun y : _115098 => @lem5129731 _115095 _115098 t s g y x)). Qed.
Lemma lem5129733 {_115098 : Type'} : (@ex _115098) = (@ex _115098).
Proof. exact (eq_refl (@ex _115098)). Qed.
Lemma lem5129734 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term150 _115095 _115098 t s g x) = (term138 _115095 _115098 t s g x).
Proof. exact (MK_COMB (@lem5129733 _115098) (@lem5129732 _115095 _115098 t s g x)). Qed.
Lemma lem5129735 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term151 _115095 _115098 t s g) = (term139 _115095 _115098 t s g).
Proof. exact (fun_ext (fun x : _115095 => @lem5129734 _115095 _115098 t s g x)). Qed.
Lemma lem5129736 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5129737 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term143 _115095 _115098 t s g) = (term140 _115095 _115098 t s g).
Proof. exact (MK_COMB (@lem5129736 _115095) (@lem5129735 _115095 _115098 t s g)). Qed.
Lemma lem5129738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5129739 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term152 _115095 _115098 t s g) = (term153 _115095 _115098 t s g).
Proof. exact (MK_COMB (@lem5129738) (@lem5129737 _115095 _115098 t s g)). Qed.
Lemma lem5129740 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term146 _115095 _115098 t s g x) = (term137 _115095 _115098 t s g x).
Proof. exact (eq_refl (term146 _115095 _115098 t s g x)). Qed.
Lemma lem5129741 {_115095 _115098 : Type'} (y : _115095 -> _115098) (x : _115095) : (y x) = (y x).
Proof. exact (eq_refl (y x)). Qed.
Lemma lem5129742 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) (x : _115095) : (term154 _115095 _115098 t s g y x) = (term155 _115095 _115098 t s g y x).
Proof. exact (MK_COMB (@lem5129740 _115095 _115098 t s g x) (@lem5129741 _115095 _115098 y x)). Qed.
Lemma lem5129743 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) (x : _115095) : (term155 _115095 _115098 t s g y x) = (term156 _115095 _115098 t s g y x).
Proof. exact (eq_refl (term155 _115095 _115098 t s g y x)). Qed.
Lemma lem5129744 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) (x : _115095) : (term154 _115095 _115098 t s g y x) = (term156 _115095 _115098 t s g y x).
Proof. exact (TRANS (@lem5129742 _115095 _115098 t s g y x) (@lem5129743 _115095 _115098 t s g y x)). Qed.
Lemma lem5129745 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) : (term157 _115095 _115098 t s g y) = (term158 _115095 _115098 t s g y).
Proof. exact (fun_ext (fun x : _115095 => @lem5129744 _115095 _115098 t s g y x)). Qed.
Lemma lem5129746 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5129747 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) : (term159 _115095 _115098 t s g y) = (term160 _115095 _115098 t s g y).
Proof. exact (MK_COMB (@lem5129746 _115095) (@lem5129745 _115095 _115098 t s g y)). Qed.
Lemma lem5129748 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term161 _115095 _115098 t s g) = (term162 _115095 _115098 t s g).
Proof. exact (fun_ext (fun y : _115095 -> _115098 => @lem5129747 _115095 _115098 t s g y)). Qed.
Lemma lem5129749 {_115095 _115098 : Type'} : (@ex (_115095 -> _115098)) = (@ex (_115095 -> _115098)).
Proof. exact (eq_refl (@ex (_115095 -> _115098))). Qed.
Lemma lem5129750 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term144 _115095 _115098 t s g) = (term163 _115095 _115098 t s g).
Proof. exact (MK_COMB (@lem5129749 _115095 _115098) (@lem5129748 _115095 _115098 t s g)). Qed.
Lemma lem5129751 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : ((term143 _115095 _115098 t s g) = (term144 _115095 _115098 t s g)) = ((term140 _115095 _115098 t s g) = (term163 _115095 _115098 t s g)).
Proof. exact (MK_COMB (@lem5129739 _115095 _115098 t s g) (@lem5129750 _115095 _115098 t s g)). Qed.
Lemma lem5129752 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term140 _115095 _115098 t s g) = (term163 _115095 _115098 t s g).
Proof. exact (EQ_MP (@lem5129751 _115095 _115098 t s g) (@lem5129726 _115095 _115098 t s g)). Qed.
Lemma lem5129753 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term70 _115095 _115098 t s g) = (term163 _115095 _115098 t s g).
Proof. exact (TRANS (@lem5129722 _115095 _115098 t s g) (@lem5129752 _115095 _115098 t s g)). Qed.
Lemma lem5129754 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term80 _115095 _115098 t s) = (term164 _115095 _115098 t s).
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5129753 _115095 _115098 t s g)). Qed.
Lemma lem5129755 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5129756 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term81 _115095 _115098 t s) = (term165 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129755 _115095 _115098) (@lem5129754 _115095 _115098 t s)). Qed.
Lemma lem5129757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5129758 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term118 _115095 _115098 t s) = (term166 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129757) (@lem5129756 _115095 _115098 t s)). Qed.
Lemma lem5129760 {A B : Type'} (P : type1413 A B) : (term141 A B P) = (term142 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5129761 {_115095 _115098 : Type'} (P : type795 _115095 _115098) : (term167 _115095 _115098 P) = (term168 _115095 _115098 P).
Proof. exact (@lem5129760 (_115098 -> _115095) _115095 P). Qed.
Lemma lem5129762 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term169 _115095 _115098 t s) = (term170 _115095 _115098 t s).
Proof. exact (@lem5129761 _115095 _115098 (term171 _115095 _115098 t s)). Qed.
Lemma lem5129763 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term172 _115095 _115098 t s f) = (term100 _115095 _115098 t s f).
Proof. exact (eq_refl (term172 _115095 _115098 t s f)). Qed.
Lemma lem5129764 {_115095 : Type'} (y : _115095) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5129765 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (y : _115095) : (term173 _115095 _115098 t s f y) = (term174 _115095 _115098 t s f y).
Proof. exact (MK_COMB (@lem5129763 _115095 _115098 t s f) (@lem5129764 _115095 y)). Qed.
Lemma lem5129766 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term174 _115095 _115098 t s f y) = (term92 _115095 _115098 t s y f).
Proof. exact (eq_refl (term174 _115095 _115098 t s f y)). Qed.
Lemma lem5129767 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term173 _115095 _115098 t s f y) = (term92 _115095 _115098 t s y f).
Proof. exact (TRANS (@lem5129765 _115095 _115098 t s f y) (@lem5129766 _115095 _115098 t s y f)). Qed.
Lemma lem5129768 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term175 _115095 _115098 t s f) = (term100 _115095 _115098 t s f).
Proof. exact (fun_ext (fun y : _115095 => @lem5129767 _115095 _115098 t s y f)). Qed.
Lemma lem5129769 {_115095 : Type'} : (@ex _115095) = (@ex _115095).
Proof. exact (eq_refl (@ex _115095)). Qed.
Lemma lem5129770 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term176 _115095 _115098 t s f) = (term101 _115095 _115098 t s f).
Proof. exact (MK_COMB (@lem5129769 _115095) (@lem5129768 _115095 _115098 t s f)). Qed.
Lemma lem5129771 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term177 _115095 _115098 t s) = (term109 _115095 _115098 t s).
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5129770 _115095 _115098 t s f)). Qed.
Lemma lem5129772 {_115095 _115098 : Type'} : (@all (_115098 -> _115095)) = (@all (_115098 -> _115095)).
Proof. exact (eq_refl (@all (_115098 -> _115095))). Qed.
Lemma lem5129773 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term169 _115095 _115098 t s) = (term110 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129772 _115095 _115098) (@lem5129771 _115095 _115098 t s)). Qed.
Lemma lem5129774 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5129775 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term178 _115095 _115098 t s) = (term179 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129774) (@lem5129773 _115095 _115098 t s)). Qed.
Lemma lem5129776 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term172 _115095 _115098 t s f) = (term100 _115095 _115098 t s f).
Proof. exact (eq_refl (term172 _115095 _115098 t s f)). Qed.
Lemma lem5129777 {_115095 _115098 : Type'} (y : type802 _115095 _115098) (f : _115098 -> _115095) : (y f) = (y f).
Proof. exact (eq_refl (y f)). Qed.
Lemma lem5129778 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : type802 _115095 _115098) (f : _115098 -> _115095) : (term180 _115095 _115098 t s y f) = (term181 _115095 _115098 t s y f).
Proof. exact (MK_COMB (@lem5129776 _115095 _115098 t s f) (@lem5129777 _115095 _115098 y f)). Qed.
Lemma lem5129779 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : type802 _115095 _115098) (f : _115098 -> _115095) : (term181 _115095 _115098 t s y f) = (term182 _115095 _115098 t s y f).
Proof. exact (eq_refl (term181 _115095 _115098 t s y f)). Qed.
Lemma lem5129780 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : type802 _115095 _115098) (f : _115098 -> _115095) : (term180 _115095 _115098 t s y f) = (term182 _115095 _115098 t s y f).
Proof. exact (TRANS (@lem5129778 _115095 _115098 t s y f) (@lem5129779 _115095 _115098 t s y f)). Qed.
Lemma lem5129781 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : type802 _115095 _115098) : (term183 _115095 _115098 t s y) = (term184 _115095 _115098 t s y).
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5129780 _115095 _115098 t s y f)). Qed.
Lemma lem5129782 {_115095 _115098 : Type'} : (@all (_115098 -> _115095)) = (@all (_115098 -> _115095)).
Proof. exact (eq_refl (@all (_115098 -> _115095))). Qed.
Lemma lem5129783 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : type802 _115095 _115098) : (term185 _115095 _115098 t s y) = (term186 _115095 _115098 t s y).
Proof. exact (MK_COMB (@lem5129782 _115095 _115098) (@lem5129781 _115095 _115098 t s y)). Qed.
Lemma lem5129784 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term187 _115095 _115098 t s) = (term188 _115095 _115098 t s).
Proof. exact (fun_ext (fun y : type802 _115095 _115098 => @lem5129783 _115095 _115098 t s y)). Qed.
Lemma lem5129785 {_115095 _115098 : Type'} : (@ex ((_115098 -> _115095) -> _115095)) = (@ex ((_115098 -> _115095) -> _115095)).
Proof. exact (eq_refl (@ex ((_115098 -> _115095) -> _115095))). Qed.
Lemma lem5129786 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term170 _115095 _115098 t s) = (term189 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129785 _115095 _115098) (@lem5129784 _115095 _115098 t s)). Qed.
Lemma lem5129787 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term169 _115095 _115098 t s) = (term170 _115095 _115098 t s)) = ((term110 _115095 _115098 t s) = (term189 _115095 _115098 t s)).
Proof. exact (MK_COMB (@lem5129775 _115095 _115098 t s) (@lem5129786 _115095 _115098 t s)). Qed.
Lemma lem5129788 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term110 _115095 _115098 t s) = (term189 _115095 _115098 t s).
Proof. exact (EQ_MP (@lem5129787 _115095 _115098 t s) (@lem5129762 _115095 _115098 t s)). Qed.
Lemma lem5129789 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term120 _115095 _115098 t s) = (term190 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129758 _115095 _115098 t s) (@lem5129788 _115095 _115098 t s)). Qed.
Lemma lem5129791 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5129792 {_115095 _115098 : Type'} (P : type805 _115095 _115098) (Q : Prop) : (term193 _115095 _115098 P Q) = (term194 _115095 _115098 P Q).
Proof. exact (@lem5129791 (_115098 -> _115095) P Q). Qed.
Lemma lem5129793 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term195 _115095 _115098 t s) = (term196 _115095 _115098 t s).
Proof. exact (@lem5129792 _115095 _115098 (term164 _115095 _115098 t s) (term189 _115095 _115098 t s)). Qed.
Lemma lem5129794 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term197 _115095 _115098 t s g) = (term163 _115095 _115098 t s g).
Proof. exact (eq_refl (term197 _115095 _115098 t s g)). Qed.
Lemma lem5129795 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term198 _115095 _115098 t s) = (term164 _115095 _115098 t s).
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5129794 _115095 _115098 t s g)). Qed.
Lemma lem5129796 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5129797 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term199 _115095 _115098 t s) = (term165 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129796 _115095 _115098) (@lem5129795 _115095 _115098 t s)). Qed.
Lemma lem5129798 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5129799 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term200 _115095 _115098 t s) = (term166 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129798) (@lem5129797 _115095 _115098 t s)). Qed.
Lemma lem5129800 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term189 _115095 _115098 t s) = (term189 _115095 _115098 t s).
Proof. exact (eq_refl (term189 _115095 _115098 t s)). Qed.
Lemma lem5129801 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term195 _115095 _115098 t s) = (term190 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129799 _115095 _115098 t s) (@lem5129800 _115095 _115098 t s)). Qed.
Lemma lem5129802 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5129803 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term201 _115095 _115098 t s) = (term202 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129802) (@lem5129801 _115095 _115098 t s)). Qed.
Lemma lem5129804 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term197 _115095 _115098 t s g) = (term163 _115095 _115098 t s g).
Proof. exact (eq_refl (term197 _115095 _115098 t s g)). Qed.
Lemma lem5129805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5129806 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term203 _115095 _115098 t s g) = (term204 _115095 _115098 t s g).
Proof. exact (MK_COMB (@lem5129805) (@lem5129804 _115095 _115098 t s g)). Qed.
Lemma lem5129807 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term189 _115095 _115098 t s) = (term189 _115095 _115098 t s).
Proof. exact (eq_refl (term189 _115095 _115098 t s)). Qed.
Lemma lem5129808 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term205 _115095 _115098 g t s) = (term206 _115095 _115098 g t s).
Proof. exact (MK_COMB (@lem5129806 _115095 _115098 t s g) (@lem5129807 _115095 _115098 t s)). Qed.
Lemma lem5129809 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term207 _115095 _115098 t s) = (term208 _115095 _115098 t s).
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5129808 _115095 _115098 g t s)). Qed.
Lemma lem5129810 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5129811 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term196 _115095 _115098 t s) = (term209 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129810 _115095 _115098) (@lem5129809 _115095 _115098 t s)). Qed.
Lemma lem5129812 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term195 _115095 _115098 t s) = (term196 _115095 _115098 t s)) = ((term190 _115095 _115098 t s) = (term209 _115095 _115098 t s)).
Proof. exact (MK_COMB (@lem5129803 _115095 _115098 t s) (@lem5129811 _115095 _115098 t s)). Qed.
Lemma lem5129813 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term190 _115095 _115098 t s) = (term209 _115095 _115098 t s).
Proof. exact (EQ_MP (@lem5129812 _115095 _115098 t s) (@lem5129793 _115095 _115098 t s)). Qed.
Lemma lem5129815 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5129816 {_115095 _115098 : Type'} (P : type572 _115095 _115098) (Q : Prop) : (term210 _115095 _115098 P Q) = (term211 _115095 _115098 P Q).
Proof. exact (@lem5129815 (_115095 -> _115098) P Q). Qed.
Lemma lem5129817 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term212 _115095 _115098 g t s) = (term213 _115095 _115098 g t s).
Proof. exact (@lem5129816 _115095 _115098 (term162 _115095 _115098 t s g) (term189 _115095 _115098 t s)). Qed.
Lemma lem5129818 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) : (term214 _115095 _115098 t s g y) = (term160 _115095 _115098 t s g y).
Proof. exact (eq_refl (term214 _115095 _115098 t s g y)). Qed.
Lemma lem5129819 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term215 _115095 _115098 t s g) = (term162 _115095 _115098 t s g).
Proof. exact (fun_ext (fun y : _115095 -> _115098 => @lem5129818 _115095 _115098 t s g y)). Qed.
Lemma lem5129820 {_115095 _115098 : Type'} : (@ex (_115095 -> _115098)) = (@ex (_115095 -> _115098)).
Proof. exact (eq_refl (@ex (_115095 -> _115098))). Qed.
Lemma lem5129821 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term216 _115095 _115098 t s g) = (term163 _115095 _115098 t s g).
Proof. exact (MK_COMB (@lem5129820 _115095 _115098) (@lem5129819 _115095 _115098 t s g)). Qed.
Lemma lem5129822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5129823 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term217 _115095 _115098 t s g) = (term204 _115095 _115098 t s g).
Proof. exact (MK_COMB (@lem5129822) (@lem5129821 _115095 _115098 t s g)). Qed.
Lemma lem5129824 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term189 _115095 _115098 t s) = (term189 _115095 _115098 t s).
Proof. exact (eq_refl (term189 _115095 _115098 t s)). Qed.
Lemma lem5129825 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term212 _115095 _115098 g t s) = (term206 _115095 _115098 g t s).
Proof. exact (MK_COMB (@lem5129823 _115095 _115098 t s g) (@lem5129824 _115095 _115098 t s)). Qed.
Lemma lem5129826 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5129827 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term218 _115095 _115098 g t s) = (term219 _115095 _115098 g t s).
Proof. exact (MK_COMB (@lem5129826) (@lem5129825 _115095 _115098 g t s)). Qed.
Lemma lem5129828 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) : (term214 _115095 _115098 t s g y) = (term160 _115095 _115098 t s g y).
Proof. exact (eq_refl (term214 _115095 _115098 t s g y)). Qed.
Lemma lem5129829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5129830 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) : (term220 _115095 _115098 t s g y) = (term221 _115095 _115098 t s g y).
Proof. exact (MK_COMB (@lem5129829) (@lem5129828 _115095 _115098 t s g y)). Qed.
Lemma lem5129831 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term189 _115095 _115098 t s) = (term189 _115095 _115098 t s).
Proof. exact (eq_refl (term189 _115095 _115098 t s)). Qed.
Lemma lem5129832 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term222 _115095 _115098 g y t s) = (term223 _115095 _115098 g y t s).
Proof. exact (MK_COMB (@lem5129830 _115095 _115098 t s g y) (@lem5129831 _115095 _115098 t s)). Qed.
Lemma lem5129833 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term224 _115095 _115098 g t s) = (term225 _115095 _115098 g t s).
Proof. exact (fun_ext (fun y : _115095 -> _115098 => @lem5129832 _115095 _115098 g y t s)). Qed.
Lemma lem5129834 {_115095 _115098 : Type'} : (@ex (_115095 -> _115098)) = (@ex (_115095 -> _115098)).
Proof. exact (eq_refl (@ex (_115095 -> _115098))). Qed.
Lemma lem5129835 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term213 _115095 _115098 g t s) = (term226 _115095 _115098 g t s).
Proof. exact (MK_COMB (@lem5129834 _115095 _115098) (@lem5129833 _115095 _115098 g t s)). Qed.
Lemma lem5129836 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term212 _115095 _115098 g t s) = (term213 _115095 _115098 g t s)) = ((term206 _115095 _115098 g t s) = (term226 _115095 _115098 g t s)).
Proof. exact (MK_COMB (@lem5129827 _115095 _115098 g t s) (@lem5129835 _115095 _115098 g t s)). Qed.
Lemma lem5129837 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term206 _115095 _115098 g t s) = (term226 _115095 _115098 g t s).
Proof. exact (EQ_MP (@lem5129836 _115095 _115098 g t s) (@lem5129817 _115095 _115098 g t s)). Qed.
Lemma lem5129839 {A : Type'} (P : Prop) (Q : A -> Prop) : (term227 A P Q) = (term228 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5129840 {_115095 _115098 : Type'} (P : Prop) (Q : type197 _115095 _115098) : (term229 _115095 _115098 P Q) = (term230 _115095 _115098 P Q).
Proof. exact (@lem5129839 (type802 _115095 _115098) P Q). Qed.
Lemma lem5129841 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term231 _115095 _115098 g y t s) = (term232 _115095 _115098 g y t s).
Proof. exact (@lem5129840 _115095 _115098 (term160 _115095 _115098 t s g y) (term188 _115095 _115098 t s)). Qed.
Lemma lem5129842 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : type802 _115095 _115098) : (term233 _115095 _115098 t s y) = (term186 _115095 _115098 t s y).
Proof. exact (eq_refl (term233 _115095 _115098 t s y)). Qed.
Lemma lem5129843 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term234 _115095 _115098 t s) = (term188 _115095 _115098 t s).
Proof. exact (fun_ext (fun y : type802 _115095 _115098 => @lem5129842 _115095 _115098 t s y)). Qed.
Lemma lem5129844 {_115095 _115098 : Type'} : (@ex ((_115098 -> _115095) -> _115095)) = (@ex ((_115098 -> _115095) -> _115095)).
Proof. exact (eq_refl (@ex ((_115098 -> _115095) -> _115095))). Qed.
Lemma lem5129845 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term235 _115095 _115098 t s) = (term189 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129844 _115095 _115098) (@lem5129843 _115095 _115098 t s)). Qed.
Lemma lem5129846 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) : (term221 _115095 _115098 t s g y) = (term221 _115095 _115098 t s g y).
Proof. exact (eq_refl (term221 _115095 _115098 t s g y)). Qed.
Lemma lem5129847 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term231 _115095 _115098 g y t s) = (term223 _115095 _115098 g y t s).
Proof. exact (MK_COMB (@lem5129846 _115095 _115098 t s g y) (@lem5129845 _115095 _115098 t s)). Qed.
Lemma lem5129848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5129849 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term236 _115095 _115098 g y t s) = (term237 _115095 _115098 g y t s).
Proof. exact (MK_COMB (@lem5129848) (@lem5129847 _115095 _115098 g y t s)). Qed.
Lemma lem5129850 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : type802 _115095 _115098) : (term233 _115095 _115098 t s y) = (term186 _115095 _115098 t s y).
Proof. exact (eq_refl (term233 _115095 _115098 t s y)). Qed.
Lemma lem5129851 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) : (term221 _115095 _115098 t s g y) = (term221 _115095 _115098 t s g y).
Proof. exact (eq_refl (term221 _115095 _115098 t s g y)). Qed.
Lemma lem5129852 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term238 _115095 _115098 g y t s y') = (term239 _115095 _115098 g y t s y').
Proof. exact (MK_COMB (@lem5129851 _115095 _115098 t s g y) (@lem5129850 _115095 _115098 t s y')). Qed.
Lemma lem5129853 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term240 _115095 _115098 g y t s) = (term241 _115095 _115098 g y t s).
Proof. exact (fun_ext (fun y' : type802 _115095 _115098 => @lem5129852 _115095 _115098 g y t s y')). Qed.
Lemma lem5129854 {_115095 _115098 : Type'} : (@ex ((_115098 -> _115095) -> _115095)) = (@ex ((_115098 -> _115095) -> _115095)).
Proof. exact (eq_refl (@ex ((_115098 -> _115095) -> _115095))). Qed.
Lemma lem5129855 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term232 _115095 _115098 g y t s) = (term242 _115095 _115098 g y t s).
Proof. exact (MK_COMB (@lem5129854 _115095 _115098) (@lem5129853 _115095 _115098 g y t s)). Qed.
Lemma lem5129856 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term231 _115095 _115098 g y t s) = (term232 _115095 _115098 g y t s)) = ((term223 _115095 _115098 g y t s) = (term242 _115095 _115098 g y t s)).
Proof. exact (MK_COMB (@lem5129849 _115095 _115098 g y t s) (@lem5129855 _115095 _115098 g y t s)). Qed.
Lemma lem5129857 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term223 _115095 _115098 g y t s) = (term242 _115095 _115098 g y t s).
Proof. exact (EQ_MP (@lem5129856 _115095 _115098 g y t s) (@lem5129841 _115095 _115098 g y t s)). Qed.
Lemma lem5129858 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term225 _115095 _115098 g t s) = (term243 _115095 _115098 g t s).
Proof. exact (fun_ext (fun y : _115095 -> _115098 => @lem5129857 _115095 _115098 g y t s)). Qed.
Lemma lem5129859 {_115095 _115098 : Type'} : (@ex (_115095 -> _115098)) = (@ex (_115095 -> _115098)).
Proof. exact (eq_refl (@ex (_115095 -> _115098))). Qed.
Lemma lem5129860 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term226 _115095 _115098 g t s) = (term244 _115095 _115098 g t s).
Proof. exact (MK_COMB (@lem5129859 _115095 _115098) (@lem5129858 _115095 _115098 g t s)). Qed.
Lemma lem5129861 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term206 _115095 _115098 g t s) = (term244 _115095 _115098 g t s).
Proof. exact (TRANS (@lem5129837 _115095 _115098 g t s) (@lem5129860 _115095 _115098 g t s)). Qed.
Lemma lem5129862 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term208 _115095 _115098 t s) = (term245 _115095 _115098 t s).
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5129861 _115095 _115098 g t s)). Qed.
Lemma lem5129863 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5129864 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term209 _115095 _115098 t s) = (term246 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129863 _115095 _115098) (@lem5129862 _115095 _115098 t s)). Qed.
Lemma lem5129865 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term190 _115095 _115098 t s) = (term246 _115095 _115098 t s).
Proof. exact (TRANS (@lem5129813 _115095 _115098 t s) (@lem5129864 _115095 _115098 t s)). Qed.
Lemma lem5129866 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term120 _115095 _115098 t s) = (term246 _115095 _115098 t s).
Proof. exact (TRANS (@lem5129789 _115095 _115098 t s) (@lem5129865 _115095 _115098 t s)). Qed.
Lemma lem5129867 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5129868 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term122 _115095 _115098 t s) = (term247 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129867) (@lem5129866 _115095 _115098 t s)). Qed.
Lemma lem5129870 {A B : Type'} (P : type1413 A B) : (term141 A B P) = (term142 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5129871 {_115095 _115098 : Type'} (P : type795 _115095 _115098) : (term167 _115095 _115098 P) = (term168 _115095 _115098 P).
Proof. exact (@lem5129870 (_115098 -> _115095) _115095 P). Qed.
Lemma lem5129872 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term248 _115095 _115098 t s) = (term249 _115095 _115098 t s).
Proof. exact (@lem5129871 _115095 _115098 (term250 _115095 _115098 t s)). Qed.
Lemma lem5129873 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term251 _115095 _115098 t s g) = (term67 _115095 _115098 t s g).
Proof. exact (eq_refl (term251 _115095 _115098 t s g)). Qed.
Lemma lem5129874 {_115095 : Type'} (x : _115095) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5129875 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term252 _115095 _115098 t s g x) = (term253 _115095 _115098 t s g x).
Proof. exact (MK_COMB (@lem5129873 _115095 _115098 t s g) (@lem5129874 _115095 x)). Qed.
Lemma lem5129876 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term253 _115095 _115098 t s g x) = (term56 _115095 _115098 t s g x).
Proof. exact (eq_refl (term253 _115095 _115098 t s g x)). Qed.
Lemma lem5129877 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (x : _115095) : (term252 _115095 _115098 t s g x) = (term56 _115095 _115098 t s g x).
Proof. exact (TRANS (@lem5129875 _115095 _115098 t s g x) (@lem5129876 _115095 _115098 t s g x)). Qed.
Lemma lem5129878 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term254 _115095 _115098 t s g) = (term67 _115095 _115098 t s g).
Proof. exact (fun_ext (fun x : _115095 => @lem5129877 _115095 _115098 t s g x)). Qed.
Lemma lem5129879 {_115095 : Type'} : (@ex _115095) = (@ex _115095).
Proof. exact (eq_refl (@ex _115095)). Qed.
Lemma lem5129880 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term255 _115095 _115098 t s g) = (term68 _115095 _115098 t s g).
Proof. exact (MK_COMB (@lem5129879 _115095) (@lem5129878 _115095 _115098 t s g)). Qed.
Lemma lem5129881 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term256 _115095 _115098 t s) = (term78 _115095 _115098 t s).
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5129880 _115095 _115098 t s g)). Qed.
Lemma lem5129882 {_115095 _115098 : Type'} : (@all (_115098 -> _115095)) = (@all (_115098 -> _115095)).
Proof. exact (eq_refl (@all (_115098 -> _115095))). Qed.
Lemma lem5129883 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term248 _115095 _115098 t s) = (term79 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129882 _115095 _115098) (@lem5129881 _115095 _115098 t s)). Qed.
Lemma lem5129884 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5129885 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term257 _115095 _115098 t s) = (term258 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129884) (@lem5129883 _115095 _115098 t s)). Qed.
Lemma lem5129886 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) : (term251 _115095 _115098 t s g) = (term67 _115095 _115098 t s g).
Proof. exact (eq_refl (term251 _115095 _115098 t s g)). Qed.
Lemma lem5129887 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (g : _115098 -> _115095) : (x g) = (x g).
Proof. exact (eq_refl (x g)). Qed.
Lemma lem5129888 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (x : type802 _115095 _115098) (g : _115098 -> _115095) : (term259 _115095 _115098 t s x g) = (term260 _115095 _115098 t s x g).
Proof. exact (MK_COMB (@lem5129886 _115095 _115098 t s g) (@lem5129887 _115095 _115098 x g)). Qed.
Lemma lem5129889 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (x : type802 _115095 _115098) (g : _115098 -> _115095) : (term260 _115095 _115098 t s x g) = (term261 _115095 _115098 t s x g).
Proof. exact (eq_refl (term260 _115095 _115098 t s x g)). Qed.
Lemma lem5129890 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (x : type802 _115095 _115098) (g : _115098 -> _115095) : (term259 _115095 _115098 t s x g) = (term261 _115095 _115098 t s x g).
Proof. exact (TRANS (@lem5129888 _115095 _115098 t s x g) (@lem5129889 _115095 _115098 t s x g)). Qed.
Lemma lem5129891 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (x : type802 _115095 _115098) : (term262 _115095 _115098 t s x) = (term263 _115095 _115098 t s x).
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5129890 _115095 _115098 t s x g)). Qed.
Lemma lem5129892 {_115095 _115098 : Type'} : (@all (_115098 -> _115095)) = (@all (_115098 -> _115095)).
Proof. exact (eq_refl (@all (_115098 -> _115095))). Qed.
Lemma lem5129893 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (x : type802 _115095 _115098) : (term264 _115095 _115098 t s x) = (term265 _115095 _115098 t s x).
Proof. exact (MK_COMB (@lem5129892 _115095 _115098) (@lem5129891 _115095 _115098 t s x)). Qed.
Lemma lem5129894 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term266 _115095 _115098 t s) = (term267 _115095 _115098 t s).
Proof. exact (fun_ext (fun x : type802 _115095 _115098 => @lem5129893 _115095 _115098 t s x)). Qed.
Lemma lem5129895 {_115095 _115098 : Type'} : (@ex ((_115098 -> _115095) -> _115095)) = (@ex ((_115098 -> _115095) -> _115095)).
Proof. exact (eq_refl (@ex ((_115098 -> _115095) -> _115095))). Qed.
Lemma lem5129896 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term249 _115095 _115098 t s) = (term268 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129895 _115095 _115098) (@lem5129894 _115095 _115098 t s)). Qed.
Lemma lem5129897 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term248 _115095 _115098 t s) = (term249 _115095 _115098 t s)) = ((term79 _115095 _115098 t s) = (term268 _115095 _115098 t s)).
Proof. exact (MK_COMB (@lem5129885 _115095 _115098 t s) (@lem5129896 _115095 _115098 t s)). Qed.
Lemma lem5129898 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term79 _115095 _115098 t s) = (term268 _115095 _115098 t s).
Proof. exact (EQ_MP (@lem5129897 _115095 _115098 t s) (@lem5129872 _115095 _115098 t s)). Qed.
Lemma lem5129899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5129900 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term114 _115095 _115098 t s) = (term269 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129899) (@lem5129898 _115095 _115098 t s)). Qed.
Lemma lem5129902 {A : Type'} (P : Prop) (Q : A -> Prop) : (term125 A P Q) = (term126 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5129903 {_115098 : Type'} (P : Prop) (Q : _115098 -> Prop) : (term125 _115098 P Q) = (term126 _115098 P Q).
Proof. exact (@lem5129902 _115098 P Q). Qed.
Lemma lem5129904 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term270 _115095 _115098 t s y f) = (term271 _115095 _115098 t s y f).
Proof. exact (@lem5129903 _115098 (term129 _115095 y t) (term27 _115095 _115098 s y f)). Qed.
Lemma lem5129905 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) (x : _115098) : (term86 _115095 _115098 s y f x) = (term26 _115095 _115098 s y f x).
Proof. exact (eq_refl (term86 _115095 _115098 s y f x)). Qed.
Lemma lem5129906 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term272 _115095 _115098 s y f) = (term27 _115095 _115098 s y f).
Proof. exact (fun_ext (fun x : _115098 => @lem5129905 _115095 _115098 s y f x)). Qed.
Lemma lem5129907 {_115098 : Type'} : (@ex _115098) = (@ex _115098).
Proof. exact (eq_refl (@ex _115098)). Qed.
Lemma lem5129908 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term273 _115095 _115098 s y f) = (term28 _115095 _115098 s y f).
Proof. exact (MK_COMB (@lem5129907 _115098) (@lem5129906 _115095 _115098 s y f)). Qed.
Lemma lem5129909 {_115095 : Type'} (y : _115095) (t : _115095 -> Prop) : (term58 _115095 y t) = (term58 _115095 y t).
Proof. exact (eq_refl (term58 _115095 y t)). Qed.
Lemma lem5129910 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term270 _115095 _115098 t s y f) = (term94 _115095 _115098 t s y f).
Proof. exact (MK_COMB (@lem5129909 _115095 y t) (@lem5129908 _115095 _115098 s y f)). Qed.
Lemma lem5129911 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5129912 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term274 _115095 _115098 t s y f) = (term275 _115095 _115098 t s y f).
Proof. exact (MK_COMB (@lem5129911) (@lem5129910 _115095 _115098 t s y f)). Qed.
Lemma lem5129913 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) (x : _115098) : (term86 _115095 _115098 s y f x) = (term26 _115095 _115098 s y f x).
Proof. exact (eq_refl (term86 _115095 _115098 s y f x)). Qed.
Lemma lem5129914 {_115095 : Type'} (y : _115095) (t : _115095 -> Prop) : (term58 _115095 y t) = (term58 _115095 y t).
Proof. exact (eq_refl (term58 _115095 y t)). Qed.
Lemma lem5129915 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) (x : _115098) : (term276 _115095 _115098 t s y f x) = (term277 _115095 _115098 t s y f x).
Proof. exact (MK_COMB (@lem5129914 _115095 y t) (@lem5129913 _115095 _115098 s y f x)). Qed.
Lemma lem5129916 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term278 _115095 _115098 t s y f) = (term279 _115095 _115098 t s y f).
Proof. exact (fun_ext (fun x : _115098 => @lem5129915 _115095 _115098 t s y f x)). Qed.
Lemma lem5129917 {_115098 : Type'} : (@ex _115098) = (@ex _115098).
Proof. exact (eq_refl (@ex _115098)). Qed.
Lemma lem5129918 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term271 _115095 _115098 t s y f) = (term280 _115095 _115098 t s y f).
Proof. exact (MK_COMB (@lem5129917 _115098) (@lem5129916 _115095 _115098 t s y f)). Qed.
Lemma lem5129919 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : ((term270 _115095 _115098 t s y f) = (term271 _115095 _115098 t s y f)) = ((term94 _115095 _115098 t s y f) = (term280 _115095 _115098 t s y f)).
Proof. exact (MK_COMB (@lem5129912 _115095 _115098 t s y f) (@lem5129918 _115095 _115098 t s y f)). Qed.
Lemma lem5129920 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term94 _115095 _115098 t s y f) = (term280 _115095 _115098 t s y f).
Proof. exact (EQ_MP (@lem5129919 _115095 _115098 t s y f) (@lem5129904 _115095 _115098 t s y f)). Qed.
Lemma lem5129921 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term102 _115095 _115098 t s f) = (term281 _115095 _115098 t s f).
Proof. exact (fun_ext (fun y : _115095 => @lem5129920 _115095 _115098 t s y f)). Qed.
Lemma lem5129922 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5129923 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term103 _115095 _115098 t s f) = (term282 _115095 _115098 t s f).
Proof. exact (MK_COMB (@lem5129922 _115095) (@lem5129921 _115095 _115098 t s f)). Qed.
Lemma lem5129925 {A B : Type'} (P : type1413 A B) : (term141 A B P) = (term142 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5129926 {_115095 _115098 : Type'} (P : type1413 _115095 _115098) : (term141 _115095 _115098 P) = (term142 _115095 _115098 P).
Proof. exact (@lem5129925 _115095 _115098 P). Qed.
Lemma lem5129927 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term283 _115095 _115098 t s f) = (term284 _115095 _115098 t s f).
Proof. exact (@lem5129926 _115095 _115098 (term285 _115095 _115098 t s f)). Qed.
Lemma lem5129928 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term286 _115095 _115098 t s f y) = (term279 _115095 _115098 t s y f).
Proof. exact (eq_refl (term286 _115095 _115098 t s f y)). Qed.
Lemma lem5129929 {_115098 : Type'} (x : _115098) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5129930 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) (x : _115098) : (term287 _115095 _115098 t s f y x) = (term288 _115095 _115098 t s y f x).
Proof. exact (MK_COMB (@lem5129928 _115095 _115098 t s y f) (@lem5129929 _115098 x)). Qed.
Lemma lem5129931 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) (x : _115098) : (term288 _115095 _115098 t s y f x) = (term277 _115095 _115098 t s y f x).
Proof. exact (eq_refl (term288 _115095 _115098 t s y f x)). Qed.
Lemma lem5129932 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) (x : _115098) : (term287 _115095 _115098 t s f y x) = (term277 _115095 _115098 t s y f x).
Proof. exact (TRANS (@lem5129930 _115095 _115098 t s y f x) (@lem5129931 _115095 _115098 t s y f x)). Qed.
Lemma lem5129933 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term289 _115095 _115098 t s f y) = (term279 _115095 _115098 t s y f).
Proof. exact (fun_ext (fun x : _115098 => @lem5129932 _115095 _115098 t s y f x)). Qed.
Lemma lem5129934 {_115098 : Type'} : (@ex _115098) = (@ex _115098).
Proof. exact (eq_refl (@ex _115098)). Qed.
Lemma lem5129935 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term290 _115095 _115098 t s f y) = (term280 _115095 _115098 t s y f).
Proof. exact (MK_COMB (@lem5129934 _115098) (@lem5129933 _115095 _115098 t s y f)). Qed.
Lemma lem5129936 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term291 _115095 _115098 t s f) = (term281 _115095 _115098 t s f).
Proof. exact (fun_ext (fun y : _115095 => @lem5129935 _115095 _115098 t s y f)). Qed.
Lemma lem5129937 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5129938 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term283 _115095 _115098 t s f) = (term282 _115095 _115098 t s f).
Proof. exact (MK_COMB (@lem5129937 _115095) (@lem5129936 _115095 _115098 t s f)). Qed.
Lemma lem5129939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5129940 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term292 _115095 _115098 t s f) = (term293 _115095 _115098 t s f).
Proof. exact (MK_COMB (@lem5129939) (@lem5129938 _115095 _115098 t s f)). Qed.
Lemma lem5129941 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115095) (f : _115098 -> _115095) : (term286 _115095 _115098 t s f y) = (term279 _115095 _115098 t s y f).
Proof. exact (eq_refl (term286 _115095 _115098 t s f y)). Qed.
Lemma lem5129942 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y : _115095) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5129943 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (y : _115095) : (term294 _115095 _115098 t s f x y) = (term295 _115095 _115098 t s f x y).
Proof. exact (MK_COMB (@lem5129941 _115095 _115098 t s y f) (@lem5129942 _115095 _115098 x y)). Qed.
Lemma lem5129944 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (y : _115095) : (term295 _115095 _115098 t s f x y) = (term296 _115095 _115098 t s f x y).
Proof. exact (eq_refl (term295 _115095 _115098 t s f x y)). Qed.
Lemma lem5129945 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (y : _115095) : (term294 _115095 _115098 t s f x y) = (term296 _115095 _115098 t s f x y).
Proof. exact (TRANS (@lem5129943 _115095 _115098 t s f x y) (@lem5129944 _115095 _115098 t s f x y)). Qed.
Lemma lem5129946 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) : (term297 _115095 _115098 t s f x) = (term298 _115095 _115098 t s f x).
Proof. exact (fun_ext (fun y : _115095 => @lem5129945 _115095 _115098 t s f x y)). Qed.
Lemma lem5129947 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5129948 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) : (term299 _115095 _115098 t s f x) = (term300 _115095 _115098 t s f x).
Proof. exact (MK_COMB (@lem5129947 _115095) (@lem5129946 _115095 _115098 t s f x)). Qed.
Lemma lem5129949 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term301 _115095 _115098 t s f) = (term302 _115095 _115098 t s f).
Proof. exact (fun_ext (fun x : _115095 -> _115098 => @lem5129948 _115095 _115098 t s f x)). Qed.
Lemma lem5129950 {_115095 _115098 : Type'} : (@ex (_115095 -> _115098)) = (@ex (_115095 -> _115098)).
Proof. exact (eq_refl (@ex (_115095 -> _115098))). Qed.
Lemma lem5129951 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term284 _115095 _115098 t s f) = (term303 _115095 _115098 t s f).
Proof. exact (MK_COMB (@lem5129950 _115095 _115098) (@lem5129949 _115095 _115098 t s f)). Qed.
Lemma lem5129952 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : ((term283 _115095 _115098 t s f) = (term284 _115095 _115098 t s f)) = ((term282 _115095 _115098 t s f) = (term303 _115095 _115098 t s f)).
Proof. exact (MK_COMB (@lem5129940 _115095 _115098 t s f) (@lem5129951 _115095 _115098 t s f)). Qed.
Lemma lem5129953 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term282 _115095 _115098 t s f) = (term303 _115095 _115098 t s f).
Proof. exact (EQ_MP (@lem5129952 _115095 _115098 t s f) (@lem5129927 _115095 _115098 t s f)). Qed.
Lemma lem5129954 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term103 _115095 _115098 t s f) = (term303 _115095 _115098 t s f).
Proof. exact (TRANS (@lem5129923 _115095 _115098 t s f) (@lem5129953 _115095 _115098 t s f)). Qed.
Lemma lem5129955 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term111 _115095 _115098 t s) = (term304 _115095 _115098 t s).
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5129954 _115095 _115098 t s f)). Qed.
Lemma lem5129956 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5129957 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term112 _115095 _115098 t s) = (term305 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129956 _115095 _115098) (@lem5129955 _115095 _115098 t s)). Qed.
Lemma lem5129958 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term116 _115095 _115098 t s) = (term306 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129900 _115095 _115098 t s) (@lem5129957 _115095 _115098 t s)). Qed.
Lemma lem5129960 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5129961 {_115095 _115098 : Type'} (P : type197 _115095 _115098) (Q : Prop) : (term307 _115095 _115098 P Q) = (term308 _115095 _115098 P Q).
Proof. exact (@lem5129960 (type802 _115095 _115098) P Q). Qed.
Lemma lem5129962 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term309 _115095 _115098 t s) = (term310 _115095 _115098 t s).
Proof. exact (@lem5129961 _115095 _115098 (term267 _115095 _115098 t s) (term305 _115095 _115098 t s)). Qed.
Lemma lem5129963 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (x : type802 _115095 _115098) : (term311 _115095 _115098 t s x) = (term265 _115095 _115098 t s x).
Proof. exact (eq_refl (term311 _115095 _115098 t s x)). Qed.
Lemma lem5129964 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term312 _115095 _115098 t s) = (term267 _115095 _115098 t s).
Proof. exact (fun_ext (fun x : type802 _115095 _115098 => @lem5129963 _115095 _115098 t s x)). Qed.
Lemma lem5129965 {_115095 _115098 : Type'} : (@ex ((_115098 -> _115095) -> _115095)) = (@ex ((_115098 -> _115095) -> _115095)).
Proof. exact (eq_refl (@ex ((_115098 -> _115095) -> _115095))). Qed.
Lemma lem5129966 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term313 _115095 _115098 t s) = (term268 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129965 _115095 _115098) (@lem5129964 _115095 _115098 t s)). Qed.
Lemma lem5129967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5129968 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term314 _115095 _115098 t s) = (term269 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129967) (@lem5129966 _115095 _115098 t s)). Qed.
Lemma lem5129969 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term305 _115095 _115098 t s) = (term305 _115095 _115098 t s).
Proof. exact (eq_refl (term305 _115095 _115098 t s)). Qed.
Lemma lem5129970 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term309 _115095 _115098 t s) = (term306 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129968 _115095 _115098 t s) (@lem5129969 _115095 _115098 t s)). Qed.
Lemma lem5129971 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5129972 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term315 _115095 _115098 t s) = (term316 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129971) (@lem5129970 _115095 _115098 t s)). Qed.
Lemma lem5129973 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (x : type802 _115095 _115098) : (term311 _115095 _115098 t s x) = (term265 _115095 _115098 t s x).
Proof. exact (eq_refl (term311 _115095 _115098 t s x)). Qed.
Lemma lem5129974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5129975 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (x : type802 _115095 _115098) : (term317 _115095 _115098 t s x) = (term318 _115095 _115098 t s x).
Proof. exact (MK_COMB (@lem5129974) (@lem5129973 _115095 _115098 t s x)). Qed.
Lemma lem5129976 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term305 _115095 _115098 t s) = (term305 _115095 _115098 t s).
Proof. exact (eq_refl (term305 _115095 _115098 t s)). Qed.
Lemma lem5129977 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term319 _115095 _115098 x t s) = (term320 _115095 _115098 x t s).
Proof. exact (MK_COMB (@lem5129975 _115095 _115098 t s x) (@lem5129976 _115095 _115098 t s)). Qed.
Lemma lem5129978 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term321 _115095 _115098 t s) = (term322 _115095 _115098 t s).
Proof. exact (fun_ext (fun x : type802 _115095 _115098 => @lem5129977 _115095 _115098 x t s)). Qed.
Lemma lem5129979 {_115095 _115098 : Type'} : (@ex ((_115098 -> _115095) -> _115095)) = (@ex ((_115098 -> _115095) -> _115095)).
Proof. exact (eq_refl (@ex ((_115098 -> _115095) -> _115095))). Qed.
Lemma lem5129980 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term310 _115095 _115098 t s) = (term323 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129979 _115095 _115098) (@lem5129978 _115095 _115098 t s)). Qed.
Lemma lem5129981 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term309 _115095 _115098 t s) = (term310 _115095 _115098 t s)) = ((term306 _115095 _115098 t s) = (term323 _115095 _115098 t s)).
Proof. exact (MK_COMB (@lem5129972 _115095 _115098 t s) (@lem5129980 _115095 _115098 t s)). Qed.
Lemma lem5129982 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term306 _115095 _115098 t s) = (term323 _115095 _115098 t s).
Proof. exact (EQ_MP (@lem5129981 _115095 _115098 t s) (@lem5129962 _115095 _115098 t s)). Qed.
Lemma lem5129984 {A : Type'} (P : Prop) (Q : A -> Prop) : (term227 A P Q) = (term228 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5129985 {_115095 _115098 : Type'} (P : Prop) (Q : type805 _115095 _115098) : (term324 _115095 _115098 P Q) = (term325 _115095 _115098 P Q).
Proof. exact (@lem5129984 (_115098 -> _115095) P Q). Qed.
Lemma lem5129986 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term326 _115095 _115098 x t s) = (term327 _115095 _115098 x t s).
Proof. exact (@lem5129985 _115095 _115098 (term265 _115095 _115098 t s x) (term304 _115095 _115098 t s)). Qed.
Lemma lem5129987 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term328 _115095 _115098 t s f) = (term303 _115095 _115098 t s f).
Proof. exact (eq_refl (term328 _115095 _115098 t s f)). Qed.
Lemma lem5129988 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term329 _115095 _115098 t s) = (term304 _115095 _115098 t s).
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5129987 _115095 _115098 t s f)). Qed.
Lemma lem5129989 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5129990 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term330 _115095 _115098 t s) = (term305 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129989 _115095 _115098) (@lem5129988 _115095 _115098 t s)). Qed.
Lemma lem5129991 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (x : type802 _115095 _115098) : (term318 _115095 _115098 t s x) = (term318 _115095 _115098 t s x).
Proof. exact (eq_refl (term318 _115095 _115098 t s x)). Qed.
Lemma lem5129992 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term326 _115095 _115098 x t s) = (term320 _115095 _115098 x t s).
Proof. exact (MK_COMB (@lem5129991 _115095 _115098 t s x) (@lem5129990 _115095 _115098 t s)). Qed.
Lemma lem5129993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5129994 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term331 _115095 _115098 x t s) = (term332 _115095 _115098 x t s).
Proof. exact (MK_COMB (@lem5129993) (@lem5129992 _115095 _115098 x t s)). Qed.
Lemma lem5129995 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term328 _115095 _115098 t s f) = (term303 _115095 _115098 t s f).
Proof. exact (eq_refl (term328 _115095 _115098 t s f)). Qed.
Lemma lem5129996 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (x : type802 _115095 _115098) : (term318 _115095 _115098 t s x) = (term318 _115095 _115098 t s x).
Proof. exact (eq_refl (term318 _115095 _115098 t s x)). Qed.
Lemma lem5129997 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term333 _115095 _115098 x t s f) = (term334 _115095 _115098 x t s f).
Proof. exact (MK_COMB (@lem5129996 _115095 _115098 t s x) (@lem5129995 _115095 _115098 t s f)). Qed.
Lemma lem5129998 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term335 _115095 _115098 x t s) = (term336 _115095 _115098 x t s).
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5129997 _115095 _115098 x t s f)). Qed.
Lemma lem5129999 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5130000 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term327 _115095 _115098 x t s) = (term337 _115095 _115098 x t s).
Proof. exact (MK_COMB (@lem5129999 _115095 _115098) (@lem5129998 _115095 _115098 x t s)). Qed.
Lemma lem5130001 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term326 _115095 _115098 x t s) = (term327 _115095 _115098 x t s)) = ((term320 _115095 _115098 x t s) = (term337 _115095 _115098 x t s)).
Proof. exact (MK_COMB (@lem5129994 _115095 _115098 x t s) (@lem5130000 _115095 _115098 x t s)). Qed.
Lemma lem5130002 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term320 _115095 _115098 x t s) = (term337 _115095 _115098 x t s).
Proof. exact (EQ_MP (@lem5130001 _115095 _115098 x t s) (@lem5129986 _115095 _115098 x t s)). Qed.
Lemma lem5130004 {A : Type'} (P : Prop) (Q : A -> Prop) : (term227 A P Q) = (term228 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5130005 {_115095 _115098 : Type'} (P : Prop) (Q : type572 _115095 _115098) : (term338 _115095 _115098 P Q) = (term339 _115095 _115098 P Q).
Proof. exact (@lem5130004 (_115095 -> _115098) P Q). Qed.
Lemma lem5130006 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term340 _115095 _115098 x t s f) = (term341 _115095 _115098 x t s f).
Proof. exact (@lem5130005 _115095 _115098 (term265 _115095 _115098 t s x) (term302 _115095 _115098 t s f)). Qed.
Lemma lem5130007 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) : (term342 _115095 _115098 t s f x) = (term300 _115095 _115098 t s f x).
Proof. exact (eq_refl (term342 _115095 _115098 t s f x)). Qed.
Lemma lem5130008 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term343 _115095 _115098 t s f) = (term302 _115095 _115098 t s f).
Proof. exact (fun_ext (fun x : _115095 -> _115098 => @lem5130007 _115095 _115098 t s f x)). Qed.
Lemma lem5130009 {_115095 _115098 : Type'} : (@ex (_115095 -> _115098)) = (@ex (_115095 -> _115098)).
Proof. exact (eq_refl (@ex (_115095 -> _115098))). Qed.
Lemma lem5130010 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term344 _115095 _115098 t s f) = (term303 _115095 _115098 t s f).
Proof. exact (MK_COMB (@lem5130009 _115095 _115098) (@lem5130008 _115095 _115098 t s f)). Qed.
Lemma lem5130011 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (x : type802 _115095 _115098) : (term318 _115095 _115098 t s x) = (term318 _115095 _115098 t s x).
Proof. exact (eq_refl (term318 _115095 _115098 t s x)). Qed.
Lemma lem5130012 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term340 _115095 _115098 x t s f) = (term334 _115095 _115098 x t s f).
Proof. exact (MK_COMB (@lem5130011 _115095 _115098 t s x) (@lem5130010 _115095 _115098 t s f)). Qed.
Lemma lem5130013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5130014 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term345 _115095 _115098 x t s f) = (term346 _115095 _115098 x t s f).
Proof. exact (MK_COMB (@lem5130013) (@lem5130012 _115095 _115098 x t s f)). Qed.
Lemma lem5130015 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) : (term342 _115095 _115098 t s f x) = (term300 _115095 _115098 t s f x).
Proof. exact (eq_refl (term342 _115095 _115098 t s f x)). Qed.
Lemma lem5130016 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (x : type802 _115095 _115098) : (term318 _115095 _115098 t s x) = (term318 _115095 _115098 t s x).
Proof. exact (eq_refl (term318 _115095 _115098 t s x)). Qed.
Lemma lem5130017 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x' : _115095 -> _115098) : (term347 _115095 _115098 x t s f x') = (term348 _115095 _115098 x t s f x').
Proof. exact (MK_COMB (@lem5130016 _115095 _115098 t s x) (@lem5130015 _115095 _115098 t s f x')). Qed.
Lemma lem5130018 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term349 _115095 _115098 x t s f) = (term350 _115095 _115098 x t s f).
Proof. exact (fun_ext (fun x' : _115095 -> _115098 => @lem5130017 _115095 _115098 x t s f x')). Qed.
Lemma lem5130019 {_115095 _115098 : Type'} : (@ex (_115095 -> _115098)) = (@ex (_115095 -> _115098)).
Proof. exact (eq_refl (@ex (_115095 -> _115098))). Qed.
Lemma lem5130020 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term341 _115095 _115098 x t s f) = (term351 _115095 _115098 x t s f).
Proof. exact (MK_COMB (@lem5130019 _115095 _115098) (@lem5130018 _115095 _115098 x t s f)). Qed.
Lemma lem5130021 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : ((term340 _115095 _115098 x t s f) = (term341 _115095 _115098 x t s f)) = ((term334 _115095 _115098 x t s f) = (term351 _115095 _115098 x t s f)).
Proof. exact (MK_COMB (@lem5130014 _115095 _115098 x t s f) (@lem5130020 _115095 _115098 x t s f)). Qed.
Lemma lem5130022 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term334 _115095 _115098 x t s f) = (term351 _115095 _115098 x t s f).
Proof. exact (EQ_MP (@lem5130021 _115095 _115098 x t s f) (@lem5130006 _115095 _115098 x t s f)). Qed.
Lemma lem5130023 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term336 _115095 _115098 x t s) = (term352 _115095 _115098 x t s).
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5130022 _115095 _115098 x t s f)). Qed.
Lemma lem5130024 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5130025 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term337 _115095 _115098 x t s) = (term353 _115095 _115098 x t s).
Proof. exact (MK_COMB (@lem5130024 _115095 _115098) (@lem5130023 _115095 _115098 x t s)). Qed.
Lemma lem5130026 {_115095 _115098 : Type'} (x : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term320 _115095 _115098 x t s) = (term353 _115095 _115098 x t s).
Proof. exact (TRANS (@lem5130002 _115095 _115098 x t s) (@lem5130025 _115095 _115098 x t s)). Qed.
Lemma lem5130027 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term322 _115095 _115098 t s) = (term354 _115095 _115098 t s).
Proof. exact (fun_ext (fun x : type802 _115095 _115098 => @lem5130026 _115095 _115098 x t s)). Qed.
Lemma lem5130028 {_115095 _115098 : Type'} : (@ex ((_115098 -> _115095) -> _115095)) = (@ex ((_115098 -> _115095) -> _115095)).
Proof. exact (eq_refl (@ex ((_115098 -> _115095) -> _115095))). Qed.
Lemma lem5130029 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term323 _115095 _115098 t s) = (term355 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5130028 _115095 _115098) (@lem5130027 _115095 _115098 t s)). Qed.
Lemma lem5130030 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term306 _115095 _115098 t s) = (term355 _115095 _115098 t s).
Proof. exact (TRANS (@lem5129982 _115095 _115098 t s) (@lem5130029 _115095 _115098 t s)). Qed.
Lemma lem5130031 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term116 _115095 _115098 t s) = (term355 _115095 _115098 t s).
Proof. exact (TRANS (@lem5129958 _115095 _115098 t s) (@lem5130030 _115095 _115098 t s)). Qed.
Lemma lem5130032 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term124 _115095 _115098 t s) = (term356 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5129868 _115095 _115098 t s) (@lem5130031 _115095 _115098 t s)). Qed.
Lemma lem5130036 {A : Type'} (P : A -> Prop) (Q : Prop) : (term357 A P Q) = (term358 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5130037 {_115095 _115098 : Type'} (P : type805 _115095 _115098) (Q : Prop) : (term359 _115095 _115098 P Q) = (term360 _115095 _115098 P Q).
Proof. exact (@lem5130036 (_115098 -> _115095) P Q). Qed.
Lemma lem5130038 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term361 _115095 _115098 t s) = (term362 _115095 _115098 t s).
Proof. exact (@lem5130037 _115095 _115098 (term245 _115095 _115098 t s) (term355 _115095 _115098 t s)). Qed.
Lemma lem5130039 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term363 _115095 _115098 t s g) = (term244 _115095 _115098 g t s).
Proof. exact (eq_refl (term363 _115095 _115098 t s g)). Qed.
Lemma lem5130040 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term364 _115095 _115098 t s) = (term245 _115095 _115098 t s).
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5130039 _115095 _115098 g t s)). Qed.
Lemma lem5130041 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5130042 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term365 _115095 _115098 t s) = (term246 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5130041 _115095 _115098) (@lem5130040 _115095 _115098 t s)). Qed.
Lemma lem5130043 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5130044 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term366 _115095 _115098 t s) = (term247 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5130043) (@lem5130042 _115095 _115098 t s)). Qed.
Lemma lem5130045 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term355 _115095 _115098 t s) = (term355 _115095 _115098 t s).
Proof. exact (eq_refl (term355 _115095 _115098 t s)). Qed.
Lemma lem5130046 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term361 _115095 _115098 t s) = (term356 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5130044 _115095 _115098 t s) (@lem5130045 _115095 _115098 t s)). Qed.
Lemma lem5130047 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5130048 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term367 _115095 _115098 t s) = (term368 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5130047) (@lem5130046 _115095 _115098 t s)). Qed.
Lemma lem5130049 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term363 _115095 _115098 t s g) = (term244 _115095 _115098 g t s).
Proof. exact (eq_refl (term363 _115095 _115098 t s g)). Qed.
Lemma lem5130050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5130051 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term369 _115095 _115098 t s g) = (term370 _115095 _115098 g t s).
Proof. exact (MK_COMB (@lem5130050) (@lem5130049 _115095 _115098 g t s)). Qed.
Lemma lem5130052 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term355 _115095 _115098 t s) = (term355 _115095 _115098 t s).
Proof. exact (eq_refl (term355 _115095 _115098 t s)). Qed.
Lemma lem5130053 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term371 _115095 _115098 g t s) = (term372 _115095 _115098 g t s).
Proof. exact (MK_COMB (@lem5130051 _115095 _115098 g t s) (@lem5130052 _115095 _115098 t s)). Qed.
Lemma lem5130054 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term373 _115095 _115098 t s) = (term374 _115095 _115098 t s).
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5130053 _115095 _115098 g t s)). Qed.
Lemma lem5130055 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5130056 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term362 _115095 _115098 t s) = (term375 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5130055 _115095 _115098) (@lem5130054 _115095 _115098 t s)). Qed.
Lemma lem5130057 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term361 _115095 _115098 t s) = (term362 _115095 _115098 t s)) = ((term356 _115095 _115098 t s) = (term375 _115095 _115098 t s)).
Proof. exact (MK_COMB (@lem5130048 _115095 _115098 t s) (@lem5130056 _115095 _115098 t s)). Qed.
Lemma lem5130058 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term356 _115095 _115098 t s) = (term375 _115095 _115098 t s).
Proof. exact (EQ_MP (@lem5130057 _115095 _115098 t s) (@lem5130038 _115095 _115098 t s)). Qed.
Lemma lem5130062 {A : Type'} (P : A -> Prop) (Q : Prop) : (term357 A P Q) = (term358 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5130063 {_115095 _115098 : Type'} (P : type572 _115095 _115098) (Q : Prop) : (term376 _115095 _115098 P Q) = (term377 _115095 _115098 P Q).
Proof. exact (@lem5130062 (_115095 -> _115098) P Q). Qed.
Lemma lem5130064 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term378 _115095 _115098 g t s) = (term379 _115095 _115098 g t s).
Proof. exact (@lem5130063 _115095 _115098 (term243 _115095 _115098 g t s) (term355 _115095 _115098 t s)). Qed.
Lemma lem5130065 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term380 _115095 _115098 g t s y) = (term242 _115095 _115098 g y t s).
Proof. exact (eq_refl (term380 _115095 _115098 g t s y)). Qed.
Lemma lem5130066 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term381 _115095 _115098 g t s) = (term243 _115095 _115098 g t s).
Proof. exact (fun_ext (fun y : _115095 -> _115098 => @lem5130065 _115095 _115098 g y t s)). Qed.
Lemma lem5130067 {_115095 _115098 : Type'} : (@ex (_115095 -> _115098)) = (@ex (_115095 -> _115098)).
Proof. exact (eq_refl (@ex (_115095 -> _115098))). Qed.
Lemma lem5130068 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term382 _115095 _115098 g t s) = (term244 _115095 _115098 g t s).
Proof. exact (MK_COMB (@lem5130067 _115095 _115098) (@lem5130066 _115095 _115098 g t s)). Qed.
Lemma lem5130069 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5130070 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term383 _115095 _115098 g t s) = (term370 _115095 _115098 g t s).
Proof. exact (MK_COMB (@lem5130069) (@lem5130068 _115095 _115098 g t s)). Qed.
Lemma lem5130071 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term355 _115095 _115098 t s) = (term355 _115095 _115098 t s).
Proof. exact (eq_refl (term355 _115095 _115098 t s)). Qed.
Lemma lem5130072 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term378 _115095 _115098 g t s) = (term372 _115095 _115098 g t s).
Proof. exact (MK_COMB (@lem5130070 _115095 _115098 g t s) (@lem5130071 _115095 _115098 t s)). Qed.
Lemma lem5130073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5130074 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term384 _115095 _115098 g t s) = (term385 _115095 _115098 g t s).
Proof. exact (MK_COMB (@lem5130073) (@lem5130072 _115095 _115098 g t s)). Qed.
Lemma lem5130075 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term380 _115095 _115098 g t s y) = (term242 _115095 _115098 g y t s).
Proof. exact (eq_refl (term380 _115095 _115098 g t s y)). Qed.
Lemma lem5130076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5130077 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term386 _115095 _115098 g t s y) = (term387 _115095 _115098 g y t s).
Proof. exact (MK_COMB (@lem5130076) (@lem5130075 _115095 _115098 g y t s)). Qed.
Lemma lem5130078 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term355 _115095 _115098 t s) = (term355 _115095 _115098 t s).
Proof. exact (eq_refl (term355 _115095 _115098 t s)). Qed.
Lemma lem5130079 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term388 _115095 _115098 g y t s) = (term389 _115095 _115098 g y t s).
Proof. exact (MK_COMB (@lem5130077 _115095 _115098 g y t s) (@lem5130078 _115095 _115098 t s)). Qed.
Lemma lem5130080 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term390 _115095 _115098 g t s) = (term391 _115095 _115098 g t s).
Proof. exact (fun_ext (fun y : _115095 -> _115098 => @lem5130079 _115095 _115098 g y t s)). Qed.
Lemma lem5130081 {_115095 _115098 : Type'} : (@ex (_115095 -> _115098)) = (@ex (_115095 -> _115098)).
Proof. exact (eq_refl (@ex (_115095 -> _115098))). Qed.
Lemma lem5130082 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term379 _115095 _115098 g t s) = (term392 _115095 _115098 g t s).
Proof. exact (MK_COMB (@lem5130081 _115095 _115098) (@lem5130080 _115095 _115098 g t s)). Qed.
Lemma lem5130083 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term378 _115095 _115098 g t s) = (term379 _115095 _115098 g t s)) = ((term372 _115095 _115098 g t s) = (term392 _115095 _115098 g t s)).
Proof. exact (MK_COMB (@lem5130074 _115095 _115098 g t s) (@lem5130082 _115095 _115098 g t s)). Qed.
Lemma lem5130084 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term372 _115095 _115098 g t s) = (term392 _115095 _115098 g t s).
Proof. exact (EQ_MP (@lem5130083 _115095 _115098 g t s) (@lem5130064 _115095 _115098 g t s)). Qed.
Lemma lem5130086 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term393 A P Q) = (term394 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5130087 {_115095 _115098 : Type'} (P : type197 _115095 _115098) (Q : type197 _115095 _115098) : (term395 _115095 _115098 P Q) = (term396 _115095 _115098 P Q).
Proof. exact (@lem5130086 (type802 _115095 _115098) P Q). Qed.
Lemma lem5130088 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term397 _115095 _115098 g y t s) = (term398 _115095 _115098 g y t s).
Proof. exact (@lem5130087 _115095 _115098 (term241 _115095 _115098 g y t s) (term354 _115095 _115098 t s)). Qed.
Lemma lem5130089 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term399 _115095 _115098 g y t s y') = (term239 _115095 _115098 g y t s y').
Proof. exact (eq_refl (term399 _115095 _115098 g y t s y')). Qed.
Lemma lem5130090 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term400 _115095 _115098 g y t s) = (term241 _115095 _115098 g y t s).
Proof. exact (fun_ext (fun y' : type802 _115095 _115098 => @lem5130089 _115095 _115098 g y t s y')). Qed.
Lemma lem5130091 {_115095 _115098 : Type'} : (@ex ((_115098 -> _115095) -> _115095)) = (@ex ((_115098 -> _115095) -> _115095)).
Proof. exact (eq_refl (@ex ((_115098 -> _115095) -> _115095))). Qed.
Lemma lem5130092 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term401 _115095 _115098 g y t s) = (term242 _115095 _115098 g y t s).
Proof. exact (MK_COMB (@lem5130091 _115095 _115098) (@lem5130090 _115095 _115098 g y t s)). Qed.
Lemma lem5130093 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5130094 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term402 _115095 _115098 g y t s) = (term387 _115095 _115098 g y t s).
Proof. exact (MK_COMB (@lem5130093) (@lem5130092 _115095 _115098 g y t s)). Qed.
Lemma lem5130095 {_115095 _115098 : Type'} (y : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term403 _115095 _115098 t s y) = (term353 _115095 _115098 y t s).
Proof. exact (eq_refl (term403 _115095 _115098 t s y)). Qed.
Lemma lem5130096 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term404 _115095 _115098 t s) = (term354 _115095 _115098 t s).
Proof. exact (fun_ext (fun y : type802 _115095 _115098 => @lem5130095 _115095 _115098 y t s)). Qed.
Lemma lem5130097 {_115095 _115098 : Type'} : (@ex ((_115098 -> _115095) -> _115095)) = (@ex ((_115098 -> _115095) -> _115095)).
Proof. exact (eq_refl (@ex ((_115098 -> _115095) -> _115095))). Qed.
Lemma lem5130098 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term405 _115095 _115098 t s) = (term355 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5130097 _115095 _115098) (@lem5130096 _115095 _115098 t s)). Qed.
Lemma lem5130099 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term397 _115095 _115098 g y t s) = (term389 _115095 _115098 g y t s).
Proof. exact (MK_COMB (@lem5130094 _115095 _115098 g y t s) (@lem5130098 _115095 _115098 t s)). Qed.
Lemma lem5130100 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5130101 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term406 _115095 _115098 g y t s) = (term407 _115095 _115098 g y t s).
Proof. exact (MK_COMB (@lem5130100) (@lem5130099 _115095 _115098 g y t s)). Qed.
Lemma lem5130102 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term399 _115095 _115098 g y t s y') = (term239 _115095 _115098 g y t s y').
Proof. exact (eq_refl (term399 _115095 _115098 g y t s y')). Qed.
Lemma lem5130103 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5130104 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term408 _115095 _115098 g y t s y') = (term409 _115095 _115098 g y t s y').
Proof. exact (MK_COMB (@lem5130103) (@lem5130102 _115095 _115098 g y t s y')). Qed.
Lemma lem5130105 {_115095 _115098 : Type'} (y : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term403 _115095 _115098 t s y) = (term353 _115095 _115098 y t s).
Proof. exact (eq_refl (term403 _115095 _115098 t s y)). Qed.
Lemma lem5130106 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term410 _115095 _115098 g y t s y') = (term411 _115095 _115098 g y y' t s).
Proof. exact (MK_COMB (@lem5130104 _115095 _115098 g y t s y') (@lem5130105 _115095 _115098 y' t s)). Qed.
Lemma lem5130107 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term412 _115095 _115098 g y t s) = (term413 _115095 _115098 g y t s).
Proof. exact (fun_ext (fun y' : type802 _115095 _115098 => @lem5130106 _115095 _115098 g y y' t s)). Qed.
Lemma lem5130108 {_115095 _115098 : Type'} : (@ex ((_115098 -> _115095) -> _115095)) = (@ex ((_115098 -> _115095) -> _115095)).
Proof. exact (eq_refl (@ex ((_115098 -> _115095) -> _115095))). Qed.
Lemma lem5130109 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term398 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s).
Proof. exact (MK_COMB (@lem5130108 _115095 _115098) (@lem5130107 _115095 _115098 g y t s)). Qed.
Lemma lem5130110 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term397 _115095 _115098 g y t s) = (term398 _115095 _115098 g y t s)) = ((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s)).
Proof. exact (MK_COMB (@lem5130101 _115095 _115098 g y t s) (@lem5130109 _115095 _115098 g y t s)). Qed.
Lemma lem5130111 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s).
Proof. exact (EQ_MP (@lem5130110 _115095 _115098 g y t s) (@lem5130088 _115095 _115098 g y t s)). Qed.
Lemma lem5130114 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term415 _115095 _115098 g y t s) = (term415 _115095 _115098 g y t s).
Proof. exact (eq_refl (term415 _115095 _115098 g y t s)). Qed.
Lemma lem5130115 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term415 _115095 _115098 g y t s) = ((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s)).
Proof. exact (eq_refl (term415 _115095 _115098 g y t s)). Qed.
Lemma lem5130116 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term416 _115095 _115098 g y t s) = (term416 _115095 _115098 g y t s).
Proof. exact (eq_refl (term416 _115095 _115098 g y t s)). Qed.
Lemma lem5130117 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term415 _115095 _115098 g y t s) = (term415 _115095 _115098 g y t s)) = ((term415 _115095 _115098 g y t s) = ((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s))).
Proof. exact (MK_COMB (@lem5130116 _115095 _115098 g y t s) (@lem5130115 _115095 _115098 g y t s)). Qed.
Lemma lem5130118 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term415 _115095 _115098 g y t s) = ((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s)).
Proof. exact (eq_refl (term415 _115095 _115098 g y t s)). Qed.
Lemma lem5130119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5130120 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term416 _115095 _115098 g y t s) = (term417 _115095 _115098 g y t s).
Proof. exact (MK_COMB (@lem5130119) (@lem5130118 _115095 _115098 g y t s)). Qed.
Lemma lem5130121 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s)) = ((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s)).
Proof. exact (eq_refl ((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s))). Qed.
Lemma lem5130122 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term415 _115095 _115098 g y t s) = ((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s))) = (((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s)) = ((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s))).
Proof. exact (MK_COMB (@lem5130120 _115095 _115098 g y t s) (@lem5130121 _115095 _115098 g y t s)). Qed.
Lemma lem5130123 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term415 _115095 _115098 g y t s) = (term415 _115095 _115098 g y t s)) = (((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s)) = ((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s))).
Proof. exact (TRANS (@lem5130117 _115095 _115098 g y t s) (@lem5130122 _115095 _115098 g y t s)). Qed.
Lemma lem5130124 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s)) = ((term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s)).
Proof. exact (EQ_MP (@lem5130123 _115095 _115098 g y t s) (@lem5130114 _115095 _115098 g y t s)). Qed.
Lemma lem5130125 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term389 _115095 _115098 g y t s) = (term414 _115095 _115098 g y t s).
Proof. exact (EQ_MP (@lem5130124 _115095 _115098 g y t s) (@lem5130111 _115095 _115098 g y t s)). Qed.
Lemma lem5130127 {A : Type'} (P : Prop) (Q : A -> Prop) : (term125 A P Q) = (term126 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5130128 {_115095 _115098 : Type'} (P : Prop) (Q : type805 _115095 _115098) : (term418 _115095 _115098 P Q) = (term419 _115095 _115098 P Q).
Proof. exact (@lem5130127 (_115098 -> _115095) P Q). Qed.
Lemma lem5130129 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term420 _115095 _115098 g y y' t s) = (term421 _115095 _115098 g y y' t s).
Proof. exact (@lem5130128 _115095 _115098 (term239 _115095 _115098 g y t s y') (term352 _115095 _115098 y' t s)). Qed.
Lemma lem5130130 {_115095 _115098 : Type'} (y : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term422 _115095 _115098 y t s f) = (term351 _115095 _115098 y t s f).
Proof. exact (eq_refl (term422 _115095 _115098 y t s f)). Qed.
Lemma lem5130131 {_115095 _115098 : Type'} (y : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term423 _115095 _115098 y t s) = (term352 _115095 _115098 y t s).
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5130130 _115095 _115098 y t s f)). Qed.
Lemma lem5130132 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5130133 {_115095 _115098 : Type'} (y : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term424 _115095 _115098 y t s) = (term353 _115095 _115098 y t s).
Proof. exact (MK_COMB (@lem5130132 _115095 _115098) (@lem5130131 _115095 _115098 y t s)). Qed.
Lemma lem5130134 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term409 _115095 _115098 g y t s y') = (term409 _115095 _115098 g y t s y').
Proof. exact (eq_refl (term409 _115095 _115098 g y t s y')). Qed.
Lemma lem5130135 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term420 _115095 _115098 g y y' t s) = (term411 _115095 _115098 g y y' t s).
Proof. exact (MK_COMB (@lem5130134 _115095 _115098 g y t s y') (@lem5130133 _115095 _115098 y' t s)). Qed.
Lemma lem5130136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5130137 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term425 _115095 _115098 g y y' t s) = (term426 _115095 _115098 g y y' t s).
Proof. exact (MK_COMB (@lem5130136) (@lem5130135 _115095 _115098 g y y' t s)). Qed.
Lemma lem5130138 {_115095 _115098 : Type'} (y : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term422 _115095 _115098 y t s f) = (term351 _115095 _115098 y t s f).
Proof. exact (eq_refl (term422 _115095 _115098 y t s f)). Qed.
Lemma lem5130139 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term409 _115095 _115098 g y t s y') = (term409 _115095 _115098 g y t s y').
Proof. exact (eq_refl (term409 _115095 _115098 g y t s y')). Qed.
Lemma lem5130140 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term427 _115095 _115098 g y y' t s f) = (term428 _115095 _115098 g y y' t s f).
Proof. exact (MK_COMB (@lem5130139 _115095 _115098 g y t s y') (@lem5130138 _115095 _115098 y' t s f)). Qed.
Lemma lem5130141 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term429 _115095 _115098 g y y' t s) = (term430 _115095 _115098 g y y' t s).
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5130140 _115095 _115098 g y y' t s f)). Qed.
Lemma lem5130142 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5130143 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term421 _115095 _115098 g y y' t s) = (term431 _115095 _115098 g y y' t s).
Proof. exact (MK_COMB (@lem5130142 _115095 _115098) (@lem5130141 _115095 _115098 g y y' t s)). Qed.
Lemma lem5130144 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : ((term420 _115095 _115098 g y y' t s) = (term421 _115095 _115098 g y y' t s)) = ((term411 _115095 _115098 g y y' t s) = (term431 _115095 _115098 g y y' t s)).
Proof. exact (MK_COMB (@lem5130137 _115095 _115098 g y y' t s) (@lem5130143 _115095 _115098 g y y' t s)). Qed.
Lemma lem5130145 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term411 _115095 _115098 g y y' t s) = (term431 _115095 _115098 g y y' t s).
Proof. exact (EQ_MP (@lem5130144 _115095 _115098 g y y' t s) (@lem5130129 _115095 _115098 g y y' t s)). Qed.
Lemma lem5130147 {A : Type'} (P : Prop) (Q : A -> Prop) : (term125 A P Q) = (term126 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5130148 {_115095 _115098 : Type'} (P : Prop) (Q : type572 _115095 _115098) : (term432 _115095 _115098 P Q) = (term433 _115095 _115098 P Q).
Proof. exact (@lem5130147 (_115095 -> _115098) P Q). Qed.
Lemma lem5130149 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term434 _115095 _115098 g y y' t s f) = (term435 _115095 _115098 g y y' t s f).
Proof. exact (@lem5130148 _115095 _115098 (term239 _115095 _115098 g y t s y') (term350 _115095 _115098 y' t s f)). Qed.
Lemma lem5130150 {_115095 _115098 : Type'} (y : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) : (term436 _115095 _115098 y t s f x) = (term348 _115095 _115098 y t s f x).
Proof. exact (eq_refl (term436 _115095 _115098 y t s f x)). Qed.
Lemma lem5130151 {_115095 _115098 : Type'} (y : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term437 _115095 _115098 y t s f) = (term350 _115095 _115098 y t s f).
Proof. exact (fun_ext (fun x : _115095 -> _115098 => @lem5130150 _115095 _115098 y t s f x)). Qed.
Lemma lem5130152 {_115095 _115098 : Type'} : (@ex (_115095 -> _115098)) = (@ex (_115095 -> _115098)).
Proof. exact (eq_refl (@ex (_115095 -> _115098))). Qed.
Lemma lem5130153 {_115095 _115098 : Type'} (y : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term438 _115095 _115098 y t s f) = (term351 _115095 _115098 y t s f).
Proof. exact (MK_COMB (@lem5130152 _115095 _115098) (@lem5130151 _115095 _115098 y t s f)). Qed.
Lemma lem5130154 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term409 _115095 _115098 g y t s y') = (term409 _115095 _115098 g y t s y').
Proof. exact (eq_refl (term409 _115095 _115098 g y t s y')). Qed.
Lemma lem5130155 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term434 _115095 _115098 g y y' t s f) = (term428 _115095 _115098 g y y' t s f).
Proof. exact (MK_COMB (@lem5130154 _115095 _115098 g y t s y') (@lem5130153 _115095 _115098 y' t s f)). Qed.
Lemma lem5130156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5130157 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term439 _115095 _115098 g y y' t s f) = (term440 _115095 _115098 g y y' t s f).
Proof. exact (MK_COMB (@lem5130156) (@lem5130155 _115095 _115098 g y y' t s f)). Qed.
Lemma lem5130158 {_115095 _115098 : Type'} (y : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) : (term436 _115095 _115098 y t s f x) = (term348 _115095 _115098 y t s f x).
Proof. exact (eq_refl (term436 _115095 _115098 y t s f x)). Qed.
Lemma lem5130159 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term409 _115095 _115098 g y t s y') = (term409 _115095 _115098 g y t s y').
Proof. exact (eq_refl (term409 _115095 _115098 g y t s y')). Qed.
Lemma lem5130160 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) : (term441 _115095 _115098 g y y' t s f x) = (term442 _115095 _115098 g y y' t s f x).
Proof. exact (MK_COMB (@lem5130159 _115095 _115098 g y t s y') (@lem5130158 _115095 _115098 y' t s f x)). Qed.
Lemma lem5130161 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term443 _115095 _115098 g y y' t s f) = (term444 _115095 _115098 g y y' t s f).
Proof. exact (fun_ext (fun x : _115095 -> _115098 => @lem5130160 _115095 _115098 g y y' t s f x)). Qed.
Lemma lem5130162 {_115095 _115098 : Type'} : (@ex (_115095 -> _115098)) = (@ex (_115095 -> _115098)).
Proof. exact (eq_refl (@ex (_115095 -> _115098))). Qed.
Lemma lem5130163 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term435 _115095 _115098 g y y' t s f) = (term445 _115095 _115098 g y y' t s f).
Proof. exact (MK_COMB (@lem5130162 _115095 _115098) (@lem5130161 _115095 _115098 g y y' t s f)). Qed.
Lemma lem5130164 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : ((term434 _115095 _115098 g y y' t s f) = (term435 _115095 _115098 g y y' t s f)) = ((term428 _115095 _115098 g y y' t s f) = (term445 _115095 _115098 g y y' t s f)).
Proof. exact (MK_COMB (@lem5130157 _115095 _115098 g y y' t s f) (@lem5130163 _115095 _115098 g y y' t s f)). Qed.
Lemma lem5130165 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) : (term428 _115095 _115098 g y y' t s f) = (term445 _115095 _115098 g y y' t s f).
Proof. exact (EQ_MP (@lem5130164 _115095 _115098 g y y' t s f) (@lem5130149 _115095 _115098 g y y' t s f)). Qed.
Lemma lem5130166 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term430 _115095 _115098 g y y' t s) = (term446 _115095 _115098 g y y' t s).
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5130165 _115095 _115098 g y y' t s f)). Qed.
Lemma lem5130167 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5130168 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term431 _115095 _115098 g y y' t s) = (term447 _115095 _115098 g y y' t s).
Proof. exact (MK_COMB (@lem5130167 _115095 _115098) (@lem5130166 _115095 _115098 g y y' t s)). Qed.
Lemma lem5130169 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term411 _115095 _115098 g y y' t s) = (term447 _115095 _115098 g y y' t s).
Proof. exact (TRANS (@lem5130145 _115095 _115098 g y y' t s) (@lem5130168 _115095 _115098 g y y' t s)). Qed.
Lemma lem5130170 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term413 _115095 _115098 g y t s) = (term448 _115095 _115098 g y t s).
Proof. exact (fun_ext (fun y' : type802 _115095 _115098 => @lem5130169 _115095 _115098 g y y' t s)). Qed.
Lemma lem5130171 {_115095 _115098 : Type'} : (@ex ((_115098 -> _115095) -> _115095)) = (@ex ((_115098 -> _115095) -> _115095)).
Proof. exact (eq_refl (@ex ((_115098 -> _115095) -> _115095))). Qed.
Lemma lem5130172 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term414 _115095 _115098 g y t s) = (term449 _115095 _115098 g y t s).
Proof. exact (MK_COMB (@lem5130171 _115095 _115098) (@lem5130170 _115095 _115098 g y t s)). Qed.
Lemma lem5130173 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term389 _115095 _115098 g y t s) = (term449 _115095 _115098 g y t s).
Proof. exact (TRANS (@lem5130125 _115095 _115098 g y t s) (@lem5130172 _115095 _115098 g y t s)). Qed.
Lemma lem5130174 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term391 _115095 _115098 g t s) = (term450 _115095 _115098 g t s).
Proof. exact (fun_ext (fun y : _115095 -> _115098 => @lem5130173 _115095 _115098 g y t s)). Qed.
Lemma lem5130175 {_115095 _115098 : Type'} : (@ex (_115095 -> _115098)) = (@ex (_115095 -> _115098)).
Proof. exact (eq_refl (@ex (_115095 -> _115098))). Qed.
Lemma lem5130176 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term392 _115095 _115098 g t s) = (term451 _115095 _115098 g t s).
Proof. exact (MK_COMB (@lem5130175 _115095 _115098) (@lem5130174 _115095 _115098 g t s)). Qed.
Lemma lem5130177 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) : (term372 _115095 _115098 g t s) = (term451 _115095 _115098 g t s).
Proof. exact (TRANS (@lem5130084 _115095 _115098 g t s) (@lem5130176 _115095 _115098 g t s)). Qed.
Lemma lem5130178 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term374 _115095 _115098 t s) = (term452 _115095 _115098 t s).
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5130177 _115095 _115098 g t s)). Qed.
Lemma lem5130179 {_115095 _115098 : Type'} : (@ex (_115098 -> _115095)) = (@ex (_115098 -> _115095)).
Proof. exact (eq_refl (@ex (_115098 -> _115095))). Qed.
Lemma lem5130180 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term375 _115095 _115098 t s) = (term453 _115095 _115098 t s).
Proof. exact (MK_COMB (@lem5130179 _115095 _115098) (@lem5130178 _115095 _115098 t s)). Qed.
Lemma lem5130181 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term356 _115095 _115098 t s) = (term453 _115095 _115098 t s).
Proof. exact (TRANS (@lem5130058 _115095 _115098 t s) (@lem5130180 _115095 _115098 t s)). Qed.
Lemma lem5130183 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term124 _115095 _115098 t s) = (term453 _115095 _115098 t s).
Proof. exact (TRANS (@lem5130032 _115095 _115098 t s) (@lem5130181 _115095 _115098 t s)). Qed.
Lemma lem5130184 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term42 _115095 _115098 t s) = (term453 _115095 _115098 t s).
Proof. exact (TRANS (@lem5129298 _115095 _115098 t s) (@lem5130183 _115095 _115098 t s)). Qed.
Lemma lem5130185 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (h1 : term42 _115095 _115098 t s) : term453 _115095 _115098 t s.
Proof. exact (EQ_MP (@lem5130184 _115095 _115098 t s) (@lem5129161 _115095 _115098 t s h1)). Qed.
Lemma lem5130186 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) (h1 : term451 _115095 _115098 g t s) : term451 _115095 _115098 g t s.
Proof. exact (h1). Qed.
Lemma lem5130187 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (h1 : term449 _115095 _115098 g y t s) : term449 _115095 _115098 g y t s.
Proof. exact (h1). Qed.
Lemma lem5130188 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (h1 : term447 _115095 _115098 g y y' t s) : term447 _115095 _115098 g y y' t s.
Proof. exact (h1). Qed.
Lemma lem5130189 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (h1 : term445 _115095 _115098 g y y' t s f) : term445 _115095 _115098 g y y' t s f.
Proof. exact (h1). Qed.
Lemma lem5130190 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term442 _115095 _115098 g y y' t s f x) : term442 _115095 _115098 g y y' t s f x.
Proof. exact (h1). Qed.
Lemma lem5130193 {_115095 _115098 : Type'} (f : _115098 -> _115095) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem5130198 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130199 {_115095 _115098 : Type'} (f : _115095 -> _115098) (x : _115095) : (f x) = (@I (_115095 -> _115098) f x).
Proof. exact (@lem5130198 _115095 _115098 f x). Qed.
Lemma lem5130201 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y : _115095) : (x y) = (@I (_115095 -> _115098) x y).
Proof. exact (@lem5130199 _115095 _115098 x y). Qed.
Lemma lem5130202 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115095 -> _115098) (y : _115095) : (term454 _115095 _115098 f x y) = (term455 _115095 _115098 f x y).
Proof. exact (MK_COMB (@lem5130193 _115095 _115098 f) (@lem5130201 _115095 _115098 x y)). Qed.
Lemma lem5130204 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130205 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115098) : (f x) = (@I (_115098 -> _115095) f x).
Proof. exact (@lem5130204 _115098 _115095 f x). Qed.
Lemma lem5130206 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115095 -> _115098) (y : _115095) : (term455 _115095 _115098 f x y) = (term456 _115095 _115098 f x y).
Proof. exact (@lem5130205 _115095 _115098 f (@I (_115095 -> _115098) x y)). Qed.
Lemma lem5130207 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115095 -> _115098) (y : _115095) : (term454 _115095 _115098 f x y) = (term456 _115095 _115098 f x y).
Proof. exact (TRANS (@lem5130202 _115095 _115098 f x y) (@lem5130206 _115095 _115098 f x y)). Qed.
Lemma lem5130208 {_115095 : Type'} (y : _115095) : (@eq _115095 y) = (@eq _115095 y).
Proof. exact (eq_refl (@eq _115095 y)). Qed.
Lemma lem5130209 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115095 -> _115098) (y : _115095) : (y = (term454 _115095 _115098 f x y)) = (y = (term456 _115095 _115098 f x y)).
Proof. exact (MK_COMB (@lem5130208 _115095 y) (@lem5130207 _115095 _115098 f x y)). Qed.
Lemma lem5130210 {_115098 : Type'} : (@IN _115098) = (@IN _115098).
Proof. exact (eq_refl (@IN _115098)). Qed.
Lemma lem5130215 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130216 {_115095 _115098 : Type'} (f : _115095 -> _115098) (x : _115095) : (f x) = (@I (_115095 -> _115098) f x).
Proof. exact (@lem5130215 _115095 _115098 f x). Qed.
Lemma lem5130218 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y : _115095) : (x y) = (@I (_115095 -> _115098) x y).
Proof. exact (@lem5130216 _115095 _115098 x y). Qed.
Lemma lem5130219 {_115098 : Type'} (s : _115098 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5130220 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y : _115095) : (term457 _115095 _115098 x y) = (term458 _115095 _115098 x y).
Proof. exact (MK_COMB (@lem5130210 _115098) (@lem5130218 _115095 _115098 x y)). Qed.
Lemma lem5130221 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y : _115095) (s : _115098 -> Prop) : (term459 _115095 _115098 x y s) = (term460 _115095 _115098 x y s).
Proof. exact (MK_COMB (@lem5130220 _115095 _115098 x y) (@lem5130219 _115098 s)). Qed.
Lemma lem5130223 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130224 {_115098 : Type'} (f : type1364 _115098) (x : _115098) : (f x) = (@I (_115098 -> (_115098 -> Prop) -> Prop) f x).
Proof. exact (@lem5130223 _115098 (type686 _115098) f x). Qed.
Lemma lem5130225 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y : _115095) : (term458 _115095 _115098 x y) = (term461 _115095 _115098 x y).
Proof. exact (@lem5130224 _115098 (@IN _115098) (@I (_115095 -> _115098) x y)). Qed.
Lemma lem5130226 {_115098 : Type'} (s : _115098 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5130227 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y : _115095) (s : _115098 -> Prop) : (term460 _115095 _115098 x y s) = (term462 _115095 _115098 x y s).
Proof. exact (MK_COMB (@lem5130225 _115095 _115098 x y) (@lem5130226 _115098 s)). Qed.
Lemma lem5130229 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130230 {_115098 : Type'} (f : type686 _115098) (x : _115098 -> Prop) : (f x) = (@I ((_115098 -> Prop) -> Prop) f x).
Proof. exact (@lem5130229 (_115098 -> Prop) Prop f x). Qed.
Lemma lem5130231 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y : _115095) (s : _115098 -> Prop) : (term462 _115095 _115098 x y s) = (term463 _115095 _115098 x y s).
Proof. exact (@lem5130230 _115098 (term461 _115095 _115098 x y) s). Qed.
Lemma lem5130232 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y : _115095) (s : _115098 -> Prop) : (term460 _115095 _115098 x y s) = (term463 _115095 _115098 x y s).
Proof. exact (TRANS (@lem5130227 _115095 _115098 x y s) (@lem5130231 _115095 _115098 x y s)). Qed.
Lemma lem5130233 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y : _115095) (s : _115098 -> Prop) : (term459 _115095 _115098 x y s) = (term463 _115095 _115098 x y s).
Proof. exact (TRANS (@lem5130221 _115095 _115098 x y s) (@lem5130232 _115095 _115098 x y s)). Qed.
Lemma lem5130234 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5130235 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y : _115095) (s : _115098 -> Prop) : (term464 _115095 _115098 x y s) = (term465 _115095 _115098 x y s).
Proof. exact (MK_COMB (@lem5130234) (@lem5130233 _115095 _115098 x y s)). Qed.
Lemma lem5130236 {_115095 _115098 : Type'} (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (y : _115095) : (term466 _115095 _115098 s f x y) = (term467 _115095 _115098 s f x y).
Proof. exact (MK_COMB (@lem5130235 _115095 _115098 x y s) (@lem5130209 _115095 _115098 f x y)). Qed.
Lemma lem5130237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5130244 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130245 {_115095 : Type'} (f : type1364 _115095) (x : _115095) : (f x) = (@I (_115095 -> (_115095 -> Prop) -> Prop) f x).
Proof. exact (@lem5130244 _115095 (type686 _115095) f x). Qed.
Lemma lem5130246 {_115095 : Type'} (y : _115095) : (@IN _115095 y) = (@I (_115095 -> (_115095 -> Prop) -> Prop) (@IN _115095) y).
Proof. exact (@lem5130245 _115095 (@IN _115095) y). Qed.
Lemma lem5130247 {_115095 : Type'} (t : _115095 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5130248 {_115095 : Type'} (y : _115095) (t : _115095 -> Prop) : (@IN _115095 y t) = (@I (_115095 -> (_115095 -> Prop) -> Prop) (@IN _115095) y t).
Proof. exact (MK_COMB (@lem5130246 _115095 y) (@lem5130247 _115095 t)). Qed.
Lemma lem5130250 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130251 {_115095 : Type'} (f : type686 _115095) (x : _115095 -> Prop) : (f x) = (@I ((_115095 -> Prop) -> Prop) f x).
Proof. exact (@lem5130250 (_115095 -> Prop) Prop f x). Qed.
Lemma lem5130252 {_115095 : Type'} (y : _115095) (t : _115095 -> Prop) : (@I (_115095 -> (_115095 -> Prop) -> Prop) (@IN _115095) y t) = (term468 _115095 y t).
Proof. exact (@lem5130251 _115095 (@I (_115095 -> (_115095 -> Prop) -> Prop) (@IN _115095) y) t). Qed.
Lemma lem5130254 {_115095 : Type'} (y : _115095) (t : _115095 -> Prop) : (@IN _115095 y t) = (term468 _115095 y t).
Proof. exact (TRANS (@lem5130248 _115095 y t) (@lem5130252 _115095 y t)). Qed.
Lemma lem5130255 {_115095 : Type'} (y : _115095) (t : _115095 -> Prop) : (term129 _115095 y t) = (term469 _115095 y t).
Proof. exact (MK_COMB (@lem5130237) (@lem5130254 _115095 y t)). Qed.
Lemma lem5130256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5130257 {_115095 : Type'} (y : _115095) (t : _115095 -> Prop) : (term58 _115095 y t) = (term470 _115095 y t).
Proof. exact (MK_COMB (@lem5130256) (@lem5130255 _115095 y t)). Qed.
Lemma lem5130258 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (y : _115095) : (term296 _115095 _115098 t s f x y) = (term471 _115095 _115098 t s f x y).
Proof. exact (MK_COMB (@lem5130257 _115095 y t) (@lem5130236 _115095 _115098 s f x y)). Qed.
Lemma lem5130259 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) : (term298 _115095 _115098 t s f x) = (term472 _115095 _115098 t s f x).
Proof. exact (fun_ext (fun y : _115095 => @lem5130258 _115095 _115098 t s f x y)). Qed.
Lemma lem5130260 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5130261 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) : (term300 _115095 _115098 t s f x) = (term473 _115095 _115098 t s f x).
Proof. exact (MK_COMB (@lem5130260 _115095) (@lem5130259 _115095 _115098 t s f x)). Qed.
Lemma lem5130262 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5130263 {_115095 : Type'} : (@eq _115095) = (@eq _115095).
Proof. exact (eq_refl (@eq _115095)). Qed.
Lemma lem5130268 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130269 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115098) : (f x) = (@I (_115098 -> _115095) f x).
Proof. exact (@lem5130268 _115098 _115095 f x). Qed.
Lemma lem5130271 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115098) : (g y) = (@I (_115098 -> _115095) g y).
Proof. exact (@lem5130269 _115095 _115098 g y). Qed.
Lemma lem5130276 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130277 {_115095 _115098 : Type'} (f : type802 _115095 _115098) (x : _115098 -> _115095) : (f x) = (@I ((_115098 -> _115095) -> _115095) f x).
Proof. exact (@lem5130276 (_115098 -> _115095) _115095 f x). Qed.
Lemma lem5130279 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (y' g) = (@I ((_115098 -> _115095) -> _115095) y' g).
Proof. exact (@lem5130277 _115095 _115098 y' g). Qed.
Lemma lem5130280 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115098) : (term474 _115095 _115098 g y) = (term475 _115095 _115098 g y).
Proof. exact (MK_COMB (@lem5130263 _115095) (@lem5130271 _115095 _115098 g y)). Qed.
Lemma lem5130281 {_115095 _115098 : Type'} (y : _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : ((g y) = (y' g)) = ((@I (_115098 -> _115095) g y) = (@I ((_115098 -> _115095) -> _115095) y' g)).
Proof. exact (MK_COMB (@lem5130280 _115095 _115098 g y) (@lem5130279 _115095 _115098 y' g)). Qed.
Lemma lem5130282 {_115095 _115098 : Type'} (y : _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term476 _115095 _115098 y y' g) = (term477 _115095 _115098 y y' g).
Proof. exact (MK_COMB (@lem5130262) (@lem5130281 _115095 _115098 y y' g)). Qed.
Lemma lem5130283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5130290 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130291 {_115098 : Type'} (f : type1364 _115098) (x : _115098) : (f x) = (@I (_115098 -> (_115098 -> Prop) -> Prop) f x).
Proof. exact (@lem5130290 _115098 (type686 _115098) f x). Qed.
Lemma lem5130292 {_115098 : Type'} (y : _115098) : (@IN _115098 y) = (@I (_115098 -> (_115098 -> Prop) -> Prop) (@IN _115098) y).
Proof. exact (@lem5130291 _115098 (@IN _115098) y). Qed.
Lemma lem5130293 {_115098 : Type'} (s : _115098 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5130294 {_115098 : Type'} (y : _115098) (s : _115098 -> Prop) : (@IN _115098 y s) = (@I (_115098 -> (_115098 -> Prop) -> Prop) (@IN _115098) y s).
Proof. exact (MK_COMB (@lem5130292 _115098 y) (@lem5130293 _115098 s)). Qed.
Lemma lem5130296 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130297 {_115098 : Type'} (f : type686 _115098) (x : _115098 -> Prop) : (f x) = (@I ((_115098 -> Prop) -> Prop) f x).
Proof. exact (@lem5130296 (_115098 -> Prop) Prop f x). Qed.
Lemma lem5130298 {_115098 : Type'} (y : _115098) (s : _115098 -> Prop) : (@I (_115098 -> (_115098 -> Prop) -> Prop) (@IN _115098) y s) = (term468 _115098 y s).
Proof. exact (@lem5130297 _115098 (@I (_115098 -> (_115098 -> Prop) -> Prop) (@IN _115098) y) s). Qed.
Lemma lem5130300 {_115098 : Type'} (y : _115098) (s : _115098 -> Prop) : (@IN _115098 y s) = (term468 _115098 y s).
Proof. exact (TRANS (@lem5130294 _115098 y s) (@lem5130298 _115098 y s)). Qed.
Lemma lem5130301 {_115098 : Type'} (y : _115098) (s : _115098 -> Prop) : (term129 _115098 y s) = (term469 _115098 y s).
Proof. exact (MK_COMB (@lem5130283) (@lem5130300 _115098 y s)). Qed.
Lemma lem5130302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5130303 {_115098 : Type'} (y : _115098) (s : _115098 -> Prop) : (term58 _115098 y s) = (term470 _115098 y s).
Proof. exact (MK_COMB (@lem5130302) (@lem5130301 _115098 y s)). Qed.
Lemma lem5130304 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term478 _115095 _115098 s y y' g) = (term479 _115095 _115098 s y y' g).
Proof. exact (MK_COMB (@lem5130303 _115098 y s) (@lem5130282 _115095 _115098 y y' g)). Qed.
Lemma lem5130305 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term480 _115095 _115098 s y' g) = (term481 _115095 _115098 s y' g).
Proof. exact (fun_ext (fun y : _115098 => @lem5130304 _115095 _115098 s y y' g)). Qed.
Lemma lem5130306 {_115098 : Type'} : (@all _115098) = (@all _115098).
Proof. exact (eq_refl (@all _115098)). Qed.
Lemma lem5130307 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term482 _115095 _115098 s y' g) = (term483 _115095 _115098 s y' g).
Proof. exact (MK_COMB (@lem5130306 _115098) (@lem5130305 _115095 _115098 s y' g)). Qed.
Lemma lem5130308 {_115095 : Type'} : (@IN _115095) = (@IN _115095).
Proof. exact (eq_refl (@IN _115095)). Qed.
Lemma lem5130313 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130314 {_115095 _115098 : Type'} (f : type802 _115095 _115098) (x : _115098 -> _115095) : (f x) = (@I ((_115098 -> _115095) -> _115095) f x).
Proof. exact (@lem5130313 (_115098 -> _115095) _115095 f x). Qed.
Lemma lem5130316 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (y' g) = (@I ((_115098 -> _115095) -> _115095) y' g).
Proof. exact (@lem5130314 _115095 _115098 y' g). Qed.
Lemma lem5130317 {_115095 : Type'} (t : _115095 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5130318 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term484 _115095 _115098 y' g) = (term485 _115095 _115098 y' g).
Proof. exact (MK_COMB (@lem5130308 _115095) (@lem5130316 _115095 _115098 y' g)). Qed.
Lemma lem5130319 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) (t : _115095 -> Prop) : (term486 _115095 _115098 y' g t) = (term487 _115095 _115098 y' g t).
Proof. exact (MK_COMB (@lem5130318 _115095 _115098 y' g) (@lem5130317 _115095 t)). Qed.
Lemma lem5130321 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130322 {_115095 : Type'} (f : type1364 _115095) (x : _115095) : (f x) = (@I (_115095 -> (_115095 -> Prop) -> Prop) f x).
Proof. exact (@lem5130321 _115095 (type686 _115095) f x). Qed.
Lemma lem5130323 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term485 _115095 _115098 y' g) = (term488 _115095 _115098 y' g).
Proof. exact (@lem5130322 _115095 (@IN _115095) (@I ((_115098 -> _115095) -> _115095) y' g)). Qed.
Lemma lem5130324 {_115095 : Type'} (t : _115095 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5130325 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) (t : _115095 -> Prop) : (term487 _115095 _115098 y' g t) = (term489 _115095 _115098 y' g t).
Proof. exact (MK_COMB (@lem5130323 _115095 _115098 y' g) (@lem5130324 _115095 t)). Qed.
Lemma lem5130327 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130328 {_115095 : Type'} (f : type686 _115095) (x : _115095 -> Prop) : (f x) = (@I ((_115095 -> Prop) -> Prop) f x).
Proof. exact (@lem5130327 (_115095 -> Prop) Prop f x). Qed.
Lemma lem5130329 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) (t : _115095 -> Prop) : (term489 _115095 _115098 y' g t) = (term490 _115095 _115098 y' g t).
Proof. exact (@lem5130328 _115095 (term488 _115095 _115098 y' g) t). Qed.
Lemma lem5130330 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) (t : _115095 -> Prop) : (term487 _115095 _115098 y' g t) = (term490 _115095 _115098 y' g t).
Proof. exact (TRANS (@lem5130325 _115095 _115098 y' g t) (@lem5130329 _115095 _115098 y' g t)). Qed.
Lemma lem5130331 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) (t : _115095 -> Prop) : (term486 _115095 _115098 y' g t) = (term490 _115095 _115098 y' g t).
Proof. exact (TRANS (@lem5130319 _115095 _115098 y' g t) (@lem5130330 _115095 _115098 y' g t)). Qed.
Lemma lem5130332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5130333 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) (t : _115095 -> Prop) : (term491 _115095 _115098 y' g t) = (term492 _115095 _115098 y' g t).
Proof. exact (MK_COMB (@lem5130332) (@lem5130331 _115095 _115098 y' g t)). Qed.
Lemma lem5130334 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term261 _115095 _115098 t s y' g) = (term493 _115095 _115098 t s y' g).
Proof. exact (MK_COMB (@lem5130333 _115095 _115098 y' g t) (@lem5130307 _115095 _115098 s y' g)). Qed.
Lemma lem5130335 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term263 _115095 _115098 t s y') = (term494 _115095 _115098 t s y').
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5130334 _115095 _115098 t s y' g)). Qed.
Lemma lem5130336 {_115095 _115098 : Type'} : (@all (_115098 -> _115095)) = (@all (_115098 -> _115095)).
Proof. exact (eq_refl (@all (_115098 -> _115095))). Qed.
Lemma lem5130337 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term265 _115095 _115098 t s y') = (term495 _115095 _115098 t s y').
Proof. exact (MK_COMB (@lem5130336 _115095 _115098) (@lem5130335 _115095 _115098 t s y')). Qed.
Lemma lem5130338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5130339 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term318 _115095 _115098 t s y') = (term496 _115095 _115098 t s y').
Proof. exact (MK_COMB (@lem5130338) (@lem5130337 _115095 _115098 t s y')). Qed.
Lemma lem5130340 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) : (term348 _115095 _115098 y' t s f x) = (term497 _115095 _115098 y' t s f x).
Proof. exact (MK_COMB (@lem5130339 _115095 _115098 t s y') (@lem5130261 _115095 _115098 t s f x)). Qed.
Lemma lem5130341 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5130342 {_115095 : Type'} : (@eq _115095) = (@eq _115095).
Proof. exact (eq_refl (@eq _115095)). Qed.
Lemma lem5130347 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130348 {_115095 _115098 : Type'} (f : type802 _115095 _115098) (x : _115098 -> _115095) : (f x) = (@I ((_115098 -> _115095) -> _115095) f x).
Proof. exact (@lem5130347 (_115098 -> _115095) _115095 f x). Qed.
Lemma lem5130350 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (y' f) = (@I ((_115098 -> _115095) -> _115095) y' f).
Proof. exact (@lem5130348 _115095 _115098 y' f). Qed.
Lemma lem5130355 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130357 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115098) : (f x) = (@I (_115098 -> _115095) f x).
Proof. exact (@lem5130355 _115098 _115095 f x). Qed.
Lemma lem5130358 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term498 _115095 _115098 y' f) = (term499 _115095 _115098 y' f).
Proof. exact (MK_COMB (@lem5130342 _115095) (@lem5130350 _115095 _115098 y' f)). Qed.
Lemma lem5130359 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) (x : _115098) : ((y' f) = (f x)) = ((@I ((_115098 -> _115095) -> _115095) y' f) = (@I (_115098 -> _115095) f x)).
Proof. exact (MK_COMB (@lem5130358 _115095 _115098 y' f) (@lem5130357 _115095 _115098 f x)). Qed.
Lemma lem5130360 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) (x : _115098) : (term500 _115095 _115098 y' f x) = (term501 _115095 _115098 y' f x).
Proof. exact (MK_COMB (@lem5130341) (@lem5130359 _115095 _115098 y' f x)). Qed.
Lemma lem5130361 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5130368 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130369 {_115098 : Type'} (f : type1364 _115098) (x : _115098) : (f x) = (@I (_115098 -> (_115098 -> Prop) -> Prop) f x).
Proof. exact (@lem5130368 _115098 (type686 _115098) f x). Qed.
Lemma lem5130370 {_115098 : Type'} (x : _115098) : (@IN _115098 x) = (@I (_115098 -> (_115098 -> Prop) -> Prop) (@IN _115098) x).
Proof. exact (@lem5130369 _115098 (@IN _115098) x). Qed.
Lemma lem5130371 {_115098 : Type'} (s : _115098 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5130372 {_115098 : Type'} (x : _115098) (s : _115098 -> Prop) : (@IN _115098 x s) = (@I (_115098 -> (_115098 -> Prop) -> Prop) (@IN _115098) x s).
Proof. exact (MK_COMB (@lem5130370 _115098 x) (@lem5130371 _115098 s)). Qed.
Lemma lem5130374 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130375 {_115098 : Type'} (f : type686 _115098) (x : _115098 -> Prop) : (f x) = (@I ((_115098 -> Prop) -> Prop) f x).
Proof. exact (@lem5130374 (_115098 -> Prop) Prop f x). Qed.
Lemma lem5130376 {_115098 : Type'} (x : _115098) (s : _115098 -> Prop) : (@I (_115098 -> (_115098 -> Prop) -> Prop) (@IN _115098) x s) = (term468 _115098 x s).
Proof. exact (@lem5130375 _115098 (@I (_115098 -> (_115098 -> Prop) -> Prop) (@IN _115098) x) s). Qed.
Lemma lem5130378 {_115098 : Type'} (x : _115098) (s : _115098 -> Prop) : (@IN _115098 x s) = (term468 _115098 x s).
Proof. exact (TRANS (@lem5130372 _115098 x s) (@lem5130376 _115098 x s)). Qed.
Lemma lem5130379 {_115098 : Type'} (x : _115098) (s : _115098 -> Prop) : (term129 _115098 x s) = (term469 _115098 x s).
Proof. exact (MK_COMB (@lem5130361) (@lem5130378 _115098 x s)). Qed.
Lemma lem5130380 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5130381 {_115098 : Type'} (x : _115098) (s : _115098 -> Prop) : (term58 _115098 x s) = (term470 _115098 x s).
Proof. exact (MK_COMB (@lem5130380) (@lem5130379 _115098 x s)). Qed.
Lemma lem5130382 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) (x : _115098) : (term502 _115095 _115098 s y' f x) = (term503 _115095 _115098 s y' f x).
Proof. exact (MK_COMB (@lem5130381 _115098 x s) (@lem5130360 _115095 _115098 y' f x)). Qed.
Lemma lem5130383 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term504 _115095 _115098 s y' f) = (term505 _115095 _115098 s y' f).
Proof. exact (fun_ext (fun x : _115098 => @lem5130382 _115095 _115098 s y' f x)). Qed.
Lemma lem5130384 {_115098 : Type'} : (@all _115098) = (@all _115098).
Proof. exact (eq_refl (@all _115098)). Qed.
Lemma lem5130385 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term506 _115095 _115098 s y' f) = (term507 _115095 _115098 s y' f).
Proof. exact (MK_COMB (@lem5130384 _115098) (@lem5130383 _115095 _115098 s y' f)). Qed.
Lemma lem5130386 {_115095 : Type'} : (@IN _115095) = (@IN _115095).
Proof. exact (eq_refl (@IN _115095)). Qed.
Lemma lem5130391 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130392 {_115095 _115098 : Type'} (f : type802 _115095 _115098) (x : _115098 -> _115095) : (f x) = (@I ((_115098 -> _115095) -> _115095) f x).
Proof. exact (@lem5130391 (_115098 -> _115095) _115095 f x). Qed.
Lemma lem5130394 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (y' f) = (@I ((_115098 -> _115095) -> _115095) y' f).
Proof. exact (@lem5130392 _115095 _115098 y' f). Qed.
Lemma lem5130395 {_115095 : Type'} (t : _115095 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5130396 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term484 _115095 _115098 y' f) = (term485 _115095 _115098 y' f).
Proof. exact (MK_COMB (@lem5130386 _115095) (@lem5130394 _115095 _115098 y' f)). Qed.
Lemma lem5130397 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) (t : _115095 -> Prop) : (term486 _115095 _115098 y' f t) = (term487 _115095 _115098 y' f t).
Proof. exact (MK_COMB (@lem5130396 _115095 _115098 y' f) (@lem5130395 _115095 t)). Qed.
Lemma lem5130399 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130400 {_115095 : Type'} (f : type1364 _115095) (x : _115095) : (f x) = (@I (_115095 -> (_115095 -> Prop) -> Prop) f x).
Proof. exact (@lem5130399 _115095 (type686 _115095) f x). Qed.
Lemma lem5130401 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term485 _115095 _115098 y' f) = (term488 _115095 _115098 y' f).
Proof. exact (@lem5130400 _115095 (@IN _115095) (@I ((_115098 -> _115095) -> _115095) y' f)). Qed.
Lemma lem5130402 {_115095 : Type'} (t : _115095 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5130403 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) (t : _115095 -> Prop) : (term487 _115095 _115098 y' f t) = (term489 _115095 _115098 y' f t).
Proof. exact (MK_COMB (@lem5130401 _115095 _115098 y' f) (@lem5130402 _115095 t)). Qed.
Lemma lem5130405 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130406 {_115095 : Type'} (f : type686 _115095) (x : _115095 -> Prop) : (f x) = (@I ((_115095 -> Prop) -> Prop) f x).
Proof. exact (@lem5130405 (_115095 -> Prop) Prop f x). Qed.
Lemma lem5130407 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) (t : _115095 -> Prop) : (term489 _115095 _115098 y' f t) = (term490 _115095 _115098 y' f t).
Proof. exact (@lem5130406 _115095 (term488 _115095 _115098 y' f) t). Qed.
Lemma lem5130408 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) (t : _115095 -> Prop) : (term487 _115095 _115098 y' f t) = (term490 _115095 _115098 y' f t).
Proof. exact (TRANS (@lem5130403 _115095 _115098 y' f t) (@lem5130407 _115095 _115098 y' f t)). Qed.
Lemma lem5130409 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) (t : _115095 -> Prop) : (term486 _115095 _115098 y' f t) = (term490 _115095 _115098 y' f t).
Proof. exact (TRANS (@lem5130397 _115095 _115098 y' f t) (@lem5130408 _115095 _115098 y' f t)). Qed.
Lemma lem5130410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5130411 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) (t : _115095 -> Prop) : (term491 _115095 _115098 y' f t) = (term492 _115095 _115098 y' f t).
Proof. exact (MK_COMB (@lem5130410) (@lem5130409 _115095 _115098 y' f t)). Qed.
Lemma lem5130412 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term182 _115095 _115098 t s y' f) = (term508 _115095 _115098 t s y' f).
Proof. exact (MK_COMB (@lem5130411 _115095 _115098 y' f t) (@lem5130385 _115095 _115098 s y' f)). Qed.
Lemma lem5130413 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term184 _115095 _115098 t s y') = (term509 _115095 _115098 t s y').
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5130412 _115095 _115098 t s y' f)). Qed.
Lemma lem5130414 {_115095 _115098 : Type'} : (@all (_115098 -> _115095)) = (@all (_115098 -> _115095)).
Proof. exact (eq_refl (@all (_115098 -> _115095))). Qed.
Lemma lem5130415 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term186 _115095 _115098 t s y') = (term510 _115095 _115098 t s y').
Proof. exact (MK_COMB (@lem5130414 _115095 _115098) (@lem5130413 _115095 _115098 t s y')). Qed.
Lemma lem5130416 {_115095 : Type'} : (@eq _115095) = (@eq _115095).
Proof. exact (eq_refl (@eq _115095)). Qed.
Lemma lem5130417 {_115095 _115098 : Type'} (g : _115098 -> _115095) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem5130422 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130423 {_115095 _115098 : Type'} (f : _115095 -> _115098) (x : _115095) : (f x) = (@I (_115095 -> _115098) f x).
Proof. exact (@lem5130422 _115095 _115098 f x). Qed.
Lemma lem5130425 {_115095 _115098 : Type'} (y : _115095 -> _115098) (x : _115095) : (y x) = (@I (_115095 -> _115098) y x).
Proof. exact (@lem5130423 _115095 _115098 y x). Qed.
Lemma lem5130426 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (x : _115095) : (term454 _115095 _115098 g y x) = (term455 _115095 _115098 g y x).
Proof. exact (MK_COMB (@lem5130417 _115095 _115098 g) (@lem5130425 _115095 _115098 y x)). Qed.
Lemma lem5130428 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130429 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115098) : (f x) = (@I (_115098 -> _115095) f x).
Proof. exact (@lem5130428 _115098 _115095 f x). Qed.
Lemma lem5130430 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (x : _115095) : (term455 _115095 _115098 g y x) = (term456 _115095 _115098 g y x).
Proof. exact (@lem5130429 _115095 _115098 g (@I (_115095 -> _115098) y x)). Qed.
Lemma lem5130431 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (x : _115095) : (term454 _115095 _115098 g y x) = (term456 _115095 _115098 g y x).
Proof. exact (TRANS (@lem5130426 _115095 _115098 g y x) (@lem5130430 _115095 _115098 g y x)). Qed.
Lemma lem5130432 {_115095 : Type'} (x : _115095) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5130433 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (x : _115095) : (term511 _115095 _115098 g y x) = (term512 _115095 _115098 g y x).
Proof. exact (MK_COMB (@lem5130416 _115095) (@lem5130431 _115095 _115098 g y x)). Qed.
Lemma lem5130434 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (x : _115095) : ((term454 _115095 _115098 g y x) = x) = ((term456 _115095 _115098 g y x) = x).
Proof. exact (MK_COMB (@lem5130433 _115095 _115098 g y x) (@lem5130432 _115095 x)). Qed.
Lemma lem5130435 {_115098 : Type'} : (@IN _115098) = (@IN _115098).
Proof. exact (eq_refl (@IN _115098)). Qed.
Lemma lem5130440 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130441 {_115095 _115098 : Type'} (f : _115095 -> _115098) (x : _115095) : (f x) = (@I (_115095 -> _115098) f x).
Proof. exact (@lem5130440 _115095 _115098 f x). Qed.
Lemma lem5130443 {_115095 _115098 : Type'} (y : _115095 -> _115098) (x : _115095) : (y x) = (@I (_115095 -> _115098) y x).
Proof. exact (@lem5130441 _115095 _115098 y x). Qed.
Lemma lem5130444 {_115098 : Type'} (s : _115098 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5130445 {_115095 _115098 : Type'} (y : _115095 -> _115098) (x : _115095) : (term457 _115095 _115098 y x) = (term458 _115095 _115098 y x).
Proof. exact (MK_COMB (@lem5130435 _115098) (@lem5130443 _115095 _115098 y x)). Qed.
Lemma lem5130446 {_115095 _115098 : Type'} (y : _115095 -> _115098) (x : _115095) (s : _115098 -> Prop) : (term459 _115095 _115098 y x s) = (term460 _115095 _115098 y x s).
Proof. exact (MK_COMB (@lem5130445 _115095 _115098 y x) (@lem5130444 _115098 s)). Qed.
Lemma lem5130448 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130449 {_115098 : Type'} (f : type1364 _115098) (x : _115098) : (f x) = (@I (_115098 -> (_115098 -> Prop) -> Prop) f x).
Proof. exact (@lem5130448 _115098 (type686 _115098) f x). Qed.
Lemma lem5130450 {_115095 _115098 : Type'} (y : _115095 -> _115098) (x : _115095) : (term458 _115095 _115098 y x) = (term461 _115095 _115098 y x).
Proof. exact (@lem5130449 _115098 (@IN _115098) (@I (_115095 -> _115098) y x)). Qed.
Lemma lem5130451 {_115098 : Type'} (s : _115098 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem5130452 {_115095 _115098 : Type'} (y : _115095 -> _115098) (x : _115095) (s : _115098 -> Prop) : (term460 _115095 _115098 y x s) = (term462 _115095 _115098 y x s).
Proof. exact (MK_COMB (@lem5130450 _115095 _115098 y x) (@lem5130451 _115098 s)). Qed.
Lemma lem5130454 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130455 {_115098 : Type'} (f : type686 _115098) (x : _115098 -> Prop) : (f x) = (@I ((_115098 -> Prop) -> Prop) f x).
Proof. exact (@lem5130454 (_115098 -> Prop) Prop f x). Qed.
Lemma lem5130456 {_115095 _115098 : Type'} (y : _115095 -> _115098) (x : _115095) (s : _115098 -> Prop) : (term462 _115095 _115098 y x s) = (term463 _115095 _115098 y x s).
Proof. exact (@lem5130455 _115098 (term461 _115095 _115098 y x) s). Qed.
Lemma lem5130457 {_115095 _115098 : Type'} (y : _115095 -> _115098) (x : _115095) (s : _115098 -> Prop) : (term460 _115095 _115098 y x s) = (term463 _115095 _115098 y x s).
Proof. exact (TRANS (@lem5130452 _115095 _115098 y x s) (@lem5130456 _115095 _115098 y x s)). Qed.
Lemma lem5130458 {_115095 _115098 : Type'} (y : _115095 -> _115098) (x : _115095) (s : _115098 -> Prop) : (term459 _115095 _115098 y x s) = (term463 _115095 _115098 y x s).
Proof. exact (TRANS (@lem5130446 _115095 _115098 y x s) (@lem5130457 _115095 _115098 y x s)). Qed.
Lemma lem5130459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5130460 {_115095 _115098 : Type'} (y : _115095 -> _115098) (x : _115095) (s : _115098 -> Prop) : (term464 _115095 _115098 y x s) = (term465 _115095 _115098 y x s).
Proof. exact (MK_COMB (@lem5130459) (@lem5130458 _115095 _115098 y x s)). Qed.
Lemma lem5130461 {_115095 _115098 : Type'} (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) (x : _115095) : (term513 _115095 _115098 s g y x) = (term514 _115095 _115098 s g y x).
Proof. exact (MK_COMB (@lem5130460 _115095 _115098 y x s) (@lem5130434 _115095 _115098 g y x)). Qed.
Lemma lem5130462 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5130469 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130470 {_115095 : Type'} (f : type1364 _115095) (x : _115095) : (f x) = (@I (_115095 -> (_115095 -> Prop) -> Prop) f x).
Proof. exact (@lem5130469 _115095 (type686 _115095) f x). Qed.
Lemma lem5130471 {_115095 : Type'} (x : _115095) : (@IN _115095 x) = (@I (_115095 -> (_115095 -> Prop) -> Prop) (@IN _115095) x).
Proof. exact (@lem5130470 _115095 (@IN _115095) x). Qed.
Lemma lem5130472 {_115095 : Type'} (t : _115095 -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5130473 {_115095 : Type'} (x : _115095) (t : _115095 -> Prop) : (@IN _115095 x t) = (@I (_115095 -> (_115095 -> Prop) -> Prop) (@IN _115095) x t).
Proof. exact (MK_COMB (@lem5130471 _115095 x) (@lem5130472 _115095 t)). Qed.
Lemma lem5130475 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem5130476 {_115095 : Type'} (f : type686 _115095) (x : _115095 -> Prop) : (f x) = (@I ((_115095 -> Prop) -> Prop) f x).
Proof. exact (@lem5130475 (_115095 -> Prop) Prop f x). Qed.
Lemma lem5130477 {_115095 : Type'} (x : _115095) (t : _115095 -> Prop) : (@I (_115095 -> (_115095 -> Prop) -> Prop) (@IN _115095) x t) = (term468 _115095 x t).
Proof. exact (@lem5130476 _115095 (@I (_115095 -> (_115095 -> Prop) -> Prop) (@IN _115095) x) t). Qed.
Lemma lem5130479 {_115095 : Type'} (x : _115095) (t : _115095 -> Prop) : (@IN _115095 x t) = (term468 _115095 x t).
Proof. exact (TRANS (@lem5130473 _115095 x t) (@lem5130477 _115095 x t)). Qed.
Lemma lem5130480 {_115095 : Type'} (x : _115095) (t : _115095 -> Prop) : (term129 _115095 x t) = (term469 _115095 x t).
Proof. exact (MK_COMB (@lem5130462) (@lem5130479 _115095 x t)). Qed.
Lemma lem5130481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5130482 {_115095 : Type'} (x : _115095) (t : _115095 -> Prop) : (term58 _115095 x t) = (term470 _115095 x t).
Proof. exact (MK_COMB (@lem5130481) (@lem5130480 _115095 x t)). Qed.
Lemma lem5130483 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) (x : _115095) : (term156 _115095 _115098 t s g y x) = (term515 _115095 _115098 t s g y x).
Proof. exact (MK_COMB (@lem5130482 _115095 x t) (@lem5130461 _115095 _115098 s g y x)). Qed.
Lemma lem5130484 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) : (term158 _115095 _115098 t s g y) = (term516 _115095 _115098 t s g y).
Proof. exact (fun_ext (fun x : _115095 => @lem5130483 _115095 _115098 t s g y x)). Qed.
Lemma lem5130485 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5130486 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) : (term160 _115095 _115098 t s g y) = (term517 _115095 _115098 t s g y).
Proof. exact (MK_COMB (@lem5130485 _115095) (@lem5130484 _115095 _115098 t s g y)). Qed.
Lemma lem5130487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5130488 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) : (term221 _115095 _115098 t s g y) = (term518 _115095 _115098 t s g y).
Proof. exact (MK_COMB (@lem5130487) (@lem5130486 _115095 _115098 t s g y)). Qed.
Lemma lem5130489 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term239 _115095 _115098 g y t s y') = (term519 _115095 _115098 g y t s y').
Proof. exact (MK_COMB (@lem5130488 _115095 _115098 t s g y) (@lem5130415 _115095 _115098 t s y')). Qed.
Lemma lem5130490 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5130491 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term409 _115095 _115098 g y t s y') = (term520 _115095 _115098 g y t s y').
Proof. exact (MK_COMB (@lem5130490) (@lem5130489 _115095 _115098 g y t s y')). Qed.
Lemma lem5130492 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) : (term442 _115095 _115098 g y y' t s f x) = (term521 _115095 _115098 g y y' t s f x).
Proof. exact (MK_COMB (@lem5130491 _115095 _115098 g y t s y') (@lem5130340 _115095 _115098 y' t s f x)). Qed.
Lemma lem5130493 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term442 _115095 _115098 g y y' t s f x) : term521 _115095 _115098 g y y' t s f x.
Proof. exact (EQ_MP (@lem5130492 _115095 _115098 g y y' t s f x) (@lem5130190 _115095 _115098 g y y' t s f x h1)). Qed.
Lemma lem5130494 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term519 _115095 _115098 g y t s y'.
Proof. exact (h1). Qed.
Lemma lem5130495 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term497 _115095 _115098 y' t s f x.
Proof. exact (h1). Qed.
Lemma lem5130496 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term510 _115095 _115098 t s y'.
Proof. exact (proj2 (@lem5130494 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5130497 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term517 _115095 _115098 t s g y.
Proof. exact (proj1 (@lem5130494 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5130498 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term473 _115095 _115098 t s f x.
Proof. exact (proj2 (@lem5130495 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5130499 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term495 _115095 _115098 t s y'.
Proof. exact (proj1 (@lem5130495 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5130517 {_115095 _115098 : Type'} (s : _115098 -> Prop) (t : _115095 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) (x : _115095) : (term515 _115095 _115098 t s g y x) = (term522 _115095 _115098 s t g y x).
Proof. exact (@lem19490 (term463 _115095 _115098 y x s) (term469 _115095 x t) ((term456 _115095 _115098 g y x) = x)). Qed.
Lemma lem5130518 {_115095 _115098 : Type'} (s : _115098 -> Prop) (t : _115095 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) : (term516 _115095 _115098 t s g y) = (term523 _115095 _115098 s t g y).
Proof. exact (fun_ext (fun x : _115095 => @lem5130517 _115095 _115098 s t g y x)). Qed.
Lemma lem5130519 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5130521 {_115095 _115098 : Type'} (s : _115098 -> Prop) (t : _115095 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) : (term517 _115095 _115098 t s g y) = (term524 _115095 _115098 s t g y).
Proof. exact (MK_COMB (@lem5130519 _115095) (@lem5130518 _115095 _115098 s t g y)). Qed.
Lemma lem5130522 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term524 _115095 _115098 s t g y.
Proof. exact (EQ_MP (@lem5130521 _115095 _115098 s t g y) (@lem5130497 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5130524 {A : Type'} (P : Prop) (Q : A -> Prop) : (term525 A P Q) = (term526 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5130525 {_115098 : Type'} (P : Prop) (Q : _115098 -> Prop) : (term525 _115098 P Q) = (term526 _115098 P Q).
Proof. exact (@lem5130524 _115098 P Q). Qed.
Lemma lem5130526 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term527 _115095 _115098 t s y' f) = (term528 _115095 _115098 t s y' f).
Proof. exact (@lem5130525 _115098 (term490 _115095 _115098 y' f t) (term505 _115095 _115098 s y' f)). Qed.
Lemma lem5130527 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) (x : _115098) : (term529 _115095 _115098 s y' f x) = (term503 _115095 _115098 s y' f x).
Proof. exact (eq_refl (term529 _115095 _115098 s y' f x)). Qed.
Lemma lem5130528 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term530 _115095 _115098 s y' f) = (term505 _115095 _115098 s y' f).
Proof. exact (fun_ext (fun x : _115098 => @lem5130527 _115095 _115098 s y' f x)). Qed.
Lemma lem5130529 {_115098 : Type'} : (@all _115098) = (@all _115098).
Proof. exact (eq_refl (@all _115098)). Qed.
Lemma lem5130530 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term531 _115095 _115098 s y' f) = (term507 _115095 _115098 s y' f).
Proof. exact (MK_COMB (@lem5130529 _115098) (@lem5130528 _115095 _115098 s y' f)). Qed.
Lemma lem5130531 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) (t : _115095 -> Prop) : (term492 _115095 _115098 y' f t) = (term492 _115095 _115098 y' f t).
Proof. exact (eq_refl (term492 _115095 _115098 y' f t)). Qed.
Lemma lem5130532 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term527 _115095 _115098 t s y' f) = (term508 _115095 _115098 t s y' f).
Proof. exact (MK_COMB (@lem5130531 _115095 _115098 y' f t) (@lem5130530 _115095 _115098 s y' f)). Qed.
Lemma lem5130533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5130534 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term532 _115095 _115098 t s y' f) = (term533 _115095 _115098 t s y' f).
Proof. exact (MK_COMB (@lem5130533) (@lem5130532 _115095 _115098 t s y' f)). Qed.
Lemma lem5130535 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) (x : _115098) : (term529 _115095 _115098 s y' f x) = (term503 _115095 _115098 s y' f x).
Proof. exact (eq_refl (term529 _115095 _115098 s y' f x)). Qed.
Lemma lem5130536 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) (t : _115095 -> Prop) : (term492 _115095 _115098 y' f t) = (term492 _115095 _115098 y' f t).
Proof. exact (eq_refl (term492 _115095 _115098 y' f t)). Qed.
Lemma lem5130537 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) (x : _115098) : (term534 _115095 _115098 t s y' f x) = (term535 _115095 _115098 t s y' f x).
Proof. exact (MK_COMB (@lem5130536 _115095 _115098 y' f t) (@lem5130535 _115095 _115098 s y' f x)). Qed.
Lemma lem5130538 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term536 _115095 _115098 t s y' f) = (term537 _115095 _115098 t s y' f).
Proof. exact (fun_ext (fun x : _115098 => @lem5130537 _115095 _115098 t s y' f x)). Qed.
Lemma lem5130539 {_115098 : Type'} : (@all _115098) = (@all _115098).
Proof. exact (eq_refl (@all _115098)). Qed.
Lemma lem5130540 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term528 _115095 _115098 t s y' f) = (term538 _115095 _115098 t s y' f).
Proof. exact (MK_COMB (@lem5130539 _115098) (@lem5130538 _115095 _115098 t s y' f)). Qed.
Lemma lem5130541 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : ((term527 _115095 _115098 t s y' f) = (term528 _115095 _115098 t s y' f)) = ((term508 _115095 _115098 t s y' f) = (term538 _115095 _115098 t s y' f)).
Proof. exact (MK_COMB (@lem5130534 _115095 _115098 t s y' f) (@lem5130540 _115095 _115098 t s y' f)). Qed.
Lemma lem5130542 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term508 _115095 _115098 t s y' f) = (term538 _115095 _115098 t s y' f).
Proof. exact (EQ_MP (@lem5130541 _115095 _115098 t s y' f) (@lem5130526 _115095 _115098 t s y' f)). Qed.
Lemma lem5130543 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term509 _115095 _115098 t s y') = (term539 _115095 _115098 t s y').
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5130542 _115095 _115098 t s y' f)). Qed.
Lemma lem5130544 {_115095 _115098 : Type'} : (@all (_115098 -> _115095)) = (@all (_115098 -> _115095)).
Proof. exact (eq_refl (@all (_115098 -> _115095))). Qed.
Lemma lem5130545 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term510 _115095 _115098 t s y') = (term540 _115095 _115098 t s y').
Proof. exact (MK_COMB (@lem5130544 _115095 _115098) (@lem5130543 _115095 _115098 t s y')). Qed.
Lemma lem5130556 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) (x : _115098) : (term535 _115095 _115098 t s y' f x) = (term535 _115095 _115098 t s y' f x).
Proof. exact (eq_refl (term535 _115095 _115098 t s y' f x)). Qed.
Lemma lem5130557 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term537 _115095 _115098 t s y' f) = (term537 _115095 _115098 t s y' f).
Proof. exact (fun_ext (fun x : _115098 => @lem5130556 _115095 _115098 t s y' f x)). Qed.
Lemma lem5130558 {_115098 : Type'} : (@all _115098) = (@all _115098).
Proof. exact (eq_refl (@all _115098)). Qed.
Lemma lem5130559 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term538 _115095 _115098 t s y' f) = (term538 _115095 _115098 t s y' f).
Proof. exact (MK_COMB (@lem5130558 _115098) (@lem5130557 _115095 _115098 t s y' f)). Qed.
Lemma lem5130560 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term539 _115095 _115098 t s y') = (term539 _115095 _115098 t s y').
Proof. exact (fun_ext (fun f : _115098 -> _115095 => @lem5130559 _115095 _115098 t s y' f)). Qed.
Lemma lem5130561 {_115095 _115098 : Type'} : (@all (_115098 -> _115095)) = (@all (_115098 -> _115095)).
Proof. exact (eq_refl (@all (_115098 -> _115095))). Qed.
Lemma lem5130562 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term540 _115095 _115098 t s y') = (term540 _115095 _115098 t s y').
Proof. exact (MK_COMB (@lem5130561 _115095 _115098) (@lem5130560 _115095 _115098 t s y')). Qed.
Lemma lem5130563 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term510 _115095 _115098 t s y') = (term540 _115095 _115098 t s y').
Proof. exact (TRANS (@lem5130545 _115095 _115098 t s y') (@lem5130562 _115095 _115098 t s y')). Qed.
Lemma lem5130564 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term540 _115095 _115098 t s y'.
Proof. exact (EQ_MP (@lem5130563 _115095 _115098 t s y') (@lem5130496 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5130566 {A : Type'} (P : Prop) (Q : A -> Prop) : (term525 A P Q) = (term526 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5130567 {_115098 : Type'} (P : Prop) (Q : _115098 -> Prop) : (term525 _115098 P Q) = (term526 _115098 P Q).
Proof. exact (@lem5130566 _115098 P Q). Qed.
Lemma lem5130568 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term541 _115095 _115098 t s y' g) = (term542 _115095 _115098 t s y' g).
Proof. exact (@lem5130567 _115098 (term490 _115095 _115098 y' g t) (term481 _115095 _115098 s y' g)). Qed.
Lemma lem5130569 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term543 _115095 _115098 s y' g y) = (term479 _115095 _115098 s y y' g).
Proof. exact (eq_refl (term543 _115095 _115098 s y' g y)). Qed.
Lemma lem5130570 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term544 _115095 _115098 s y' g) = (term481 _115095 _115098 s y' g).
Proof. exact (fun_ext (fun y : _115098 => @lem5130569 _115095 _115098 s y y' g)). Qed.
Lemma lem5130571 {_115098 : Type'} : (@all _115098) = (@all _115098).
Proof. exact (eq_refl (@all _115098)). Qed.
Lemma lem5130572 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term545 _115095 _115098 s y' g) = (term483 _115095 _115098 s y' g).
Proof. exact (MK_COMB (@lem5130571 _115098) (@lem5130570 _115095 _115098 s y' g)). Qed.
Lemma lem5130573 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) (t : _115095 -> Prop) : (term492 _115095 _115098 y' g t) = (term492 _115095 _115098 y' g t).
Proof. exact (eq_refl (term492 _115095 _115098 y' g t)). Qed.
Lemma lem5130574 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term541 _115095 _115098 t s y' g) = (term493 _115095 _115098 t s y' g).
Proof. exact (MK_COMB (@lem5130573 _115095 _115098 y' g t) (@lem5130572 _115095 _115098 s y' g)). Qed.
Lemma lem5130575 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5130576 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term546 _115095 _115098 t s y' g) = (term547 _115095 _115098 t s y' g).
Proof. exact (MK_COMB (@lem5130575) (@lem5130574 _115095 _115098 t s y' g)). Qed.
Lemma lem5130577 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y : _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term543 _115095 _115098 s y' g y) = (term479 _115095 _115098 s y y' g).
Proof. exact (eq_refl (term543 _115095 _115098 s y' g y)). Qed.
Lemma lem5130578 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) (t : _115095 -> Prop) : (term492 _115095 _115098 y' g t) = (term492 _115095 _115098 y' g t).
Proof. exact (eq_refl (term492 _115095 _115098 y' g t)). Qed.
Lemma lem5130579 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term548 _115095 _115098 t s y' g y) = (term549 _115095 _115098 t s y y' g).
Proof. exact (MK_COMB (@lem5130578 _115095 _115098 y' g t) (@lem5130577 _115095 _115098 s y y' g)). Qed.
Lemma lem5130580 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term550 _115095 _115098 t s y' g) = (term551 _115095 _115098 t s y' g).
Proof. exact (fun_ext (fun y : _115098 => @lem5130579 _115095 _115098 t s y y' g)). Qed.
Lemma lem5130581 {_115098 : Type'} : (@all _115098) = (@all _115098).
Proof. exact (eq_refl (@all _115098)). Qed.
Lemma lem5130582 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term542 _115095 _115098 t s y' g) = (term552 _115095 _115098 t s y' g).
Proof. exact (MK_COMB (@lem5130581 _115098) (@lem5130580 _115095 _115098 t s y' g)). Qed.
Lemma lem5130583 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : ((term541 _115095 _115098 t s y' g) = (term542 _115095 _115098 t s y' g)) = ((term493 _115095 _115098 t s y' g) = (term552 _115095 _115098 t s y' g)).
Proof. exact (MK_COMB (@lem5130576 _115095 _115098 t s y' g) (@lem5130582 _115095 _115098 t s y' g)). Qed.
Lemma lem5130584 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term493 _115095 _115098 t s y' g) = (term552 _115095 _115098 t s y' g).
Proof. exact (EQ_MP (@lem5130583 _115095 _115098 t s y' g) (@lem5130568 _115095 _115098 t s y' g)). Qed.
Lemma lem5130585 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term494 _115095 _115098 t s y') = (term553 _115095 _115098 t s y').
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5130584 _115095 _115098 t s y' g)). Qed.
Lemma lem5130586 {_115095 _115098 : Type'} : (@all (_115098 -> _115095)) = (@all (_115098 -> _115095)).
Proof. exact (eq_refl (@all (_115098 -> _115095))). Qed.
Lemma lem5130587 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term495 _115095 _115098 t s y') = (term554 _115095 _115098 t s y').
Proof. exact (MK_COMB (@lem5130586 _115095 _115098) (@lem5130585 _115095 _115098 t s y')). Qed.
Lemma lem5130598 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y : _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term549 _115095 _115098 t s y y' g) = (term549 _115095 _115098 t s y y' g).
Proof. exact (eq_refl (term549 _115095 _115098 t s y y' g)). Qed.
Lemma lem5130599 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term551 _115095 _115098 t s y' g) = (term551 _115095 _115098 t s y' g).
Proof. exact (fun_ext (fun y : _115098 => @lem5130598 _115095 _115098 t s y y' g)). Qed.
Lemma lem5130600 {_115098 : Type'} : (@all _115098) = (@all _115098).
Proof. exact (eq_refl (@all _115098)). Qed.
Lemma lem5130601 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term552 _115095 _115098 t s y' g) = (term552 _115095 _115098 t s y' g).
Proof. exact (MK_COMB (@lem5130600 _115098) (@lem5130599 _115095 _115098 t s y' g)). Qed.
Lemma lem5130602 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term553 _115095 _115098 t s y') = (term553 _115095 _115098 t s y').
Proof. exact (fun_ext (fun g : _115098 -> _115095 => @lem5130601 _115095 _115098 t s y' g)). Qed.
Lemma lem5130603 {_115095 _115098 : Type'} : (@all (_115098 -> _115095)) = (@all (_115098 -> _115095)).
Proof. exact (eq_refl (@all (_115098 -> _115095))). Qed.
Lemma lem5130604 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term554 _115095 _115098 t s y') = (term554 _115095 _115098 t s y').
Proof. exact (MK_COMB (@lem5130603 _115095 _115098) (@lem5130602 _115095 _115098 t s y')). Qed.
Lemma lem5130605 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) : (term495 _115095 _115098 t s y') = (term554 _115095 _115098 t s y').
Proof. exact (TRANS (@lem5130587 _115095 _115098 t s y') (@lem5130604 _115095 _115098 t s y')). Qed.
Lemma lem5130606 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term554 _115095 _115098 t s y'.
Proof. exact (EQ_MP (@lem5130605 _115095 _115098 t s y') (@lem5130499 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5130624 {_115095 _115098 : Type'} (s : _115098 -> Prop) (t : _115095 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (y : _115095) : (term471 _115095 _115098 t s f x y) = (term555 _115095 _115098 s t f x y).
Proof. exact (@lem19490 (term463 _115095 _115098 x y s) (term469 _115095 y t) (y = (term456 _115095 _115098 f x y))). Qed.
Lemma lem5130625 {_115095 _115098 : Type'} (s : _115098 -> Prop) (t : _115095 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) : (term472 _115095 _115098 t s f x) = (term556 _115095 _115098 s t f x).
Proof. exact (fun_ext (fun y : _115095 => @lem5130624 _115095 _115098 s t f x y)). Qed.
Lemma lem5130626 {_115095 : Type'} : (@all _115095) = (@all _115095).
Proof. exact (eq_refl (@all _115095)). Qed.
Lemma lem5130628 {_115095 _115098 : Type'} (s : _115098 -> Prop) (t : _115095 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) : (term473 _115095 _115098 t s f x) = (term557 _115095 _115098 s t f x).
Proof. exact (MK_COMB (@lem5130626 _115095) (@lem5130625 _115095 _115098 s t f x)). Qed.
Lemma lem5130629 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term557 _115095 _115098 s t f x.
Proof. exact (EQ_MP (@lem5130628 _115095 _115098 s t f x) (@lem5130498 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5130630 {_115095 _115098 : Type'} (_66978 : _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term558 _115095 _115098 s t g y _66978.
Proof. exact (@lem5130522 _115095 _115098 g y t s y' h1 _66978). Qed.
Lemma lem5130631 {_115095 _115098 : Type'} (s : _115098 -> Prop) (t : _115095 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) (_66978 : _115095) : (term558 _115095 _115098 s t g y _66978) = (term522 _115095 _115098 s t g y _66978).
Proof. exact (eq_refl (term558 _115095 _115098 s t g y _66978)). Qed.
Lemma lem5130632 {_115095 _115098 : Type'} (_66978 : _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term522 _115095 _115098 s t g y _66978.
Proof. exact (EQ_MP (@lem5130631 _115095 _115098 s t g y _66978) (@lem5130630 _115095 _115098 _66978 g y t s y' h1)). Qed.
Lemma lem5130633 {_115095 _115098 : Type'} (_66979 : _115098 -> _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term559 _115095 _115098 t s y' _66979.
Proof. exact (@lem5130564 _115095 _115098 g y t s y' h1 _66979). Qed.
Lemma lem5130634 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (_66979 : _115098 -> _115095) : (term559 _115095 _115098 t s y' _66979) = (term538 _115095 _115098 t s y' _66979).
Proof. exact (eq_refl (term559 _115095 _115098 t s y' _66979)). Qed.
Lemma lem5130635 {_115095 _115098 : Type'} (_66979 : _115098 -> _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term538 _115095 _115098 t s y' _66979.
Proof. exact (EQ_MP (@lem5130634 _115095 _115098 t s y' _66979) (@lem5130633 _115095 _115098 _66979 g y t s y' h1)). Qed.
Lemma lem5130636 {_115095 _115098 : Type'} (_66979 : _115098 -> _115095) (_66980 : _115098) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term560 _115095 _115098 t s y' _66979 _66980.
Proof. exact (@lem5130635 _115095 _115098 _66979 g y t s y' h1 _66980). Qed.
Lemma lem5130637 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (_66979 : _115098 -> _115095) (_66980 : _115098) : (term560 _115095 _115098 t s y' _66979 _66980) = (term535 _115095 _115098 t s y' _66979 _66980).
Proof. exact (eq_refl (term560 _115095 _115098 t s y' _66979 _66980)). Qed.
Lemma lem5130638 {_115095 _115098 : Type'} (_66979 : _115098 -> _115095) (_66980 : _115098) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term535 _115095 _115098 t s y' _66979 _66980.
Proof. exact (EQ_MP (@lem5130637 _115095 _115098 t s y' _66979 _66980) (@lem5130636 _115095 _115098 _66979 _66980 g y t s y' h1)). Qed.
Lemma lem5130639 {_115095 _115098 : Type'} (_66981 : _115098 -> _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term561 _115095 _115098 t s y' _66981.
Proof. exact (@lem5130606 _115095 _115098 y' t s f x h1 _66981). Qed.
Lemma lem5130640 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (_66981 : _115098 -> _115095) : (term561 _115095 _115098 t s y' _66981) = (term552 _115095 _115098 t s y' _66981).
Proof. exact (eq_refl (term561 _115095 _115098 t s y' _66981)). Qed.
Lemma lem5130641 {_115095 _115098 : Type'} (_66981 : _115098 -> _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term552 _115095 _115098 t s y' _66981.
Proof. exact (EQ_MP (@lem5130640 _115095 _115098 t s y' _66981) (@lem5130639 _115095 _115098 _66981 y' t s f x h1)). Qed.
Lemma lem5130642 {_115095 _115098 : Type'} (_66981 : _115098 -> _115095) (_66982 : _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term562 _115095 _115098 t s y' _66981 _66982.
Proof. exact (@lem5130641 _115095 _115098 _66981 y' t s f x h1 _66982). Qed.
Lemma lem5130643 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (_66982 : _115098) (y' : type802 _115095 _115098) (_66981 : _115098 -> _115095) : (term562 _115095 _115098 t s y' _66981 _66982) = (term549 _115095 _115098 t s _66982 y' _66981).
Proof. exact (eq_refl (term562 _115095 _115098 t s y' _66981 _66982)). Qed.
Lemma lem5130644 {_115095 _115098 : Type'} (_66982 : _115098) (_66981 : _115098 -> _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term549 _115095 _115098 t s _66982 y' _66981.
Proof. exact (EQ_MP (@lem5130643 _115095 _115098 t s _66982 y' _66981) (@lem5130642 _115095 _115098 _66981 _66982 y' t s f x h1)). Qed.
Lemma lem5130645 {_115095 _115098 : Type'} (_66983 : _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term563 _115095 _115098 s t f x _66983.
Proof. exact (@lem5130629 _115095 _115098 y' t s f x h1 _66983). Qed.
Lemma lem5130646 {_115095 _115098 : Type'} (s : _115098 -> Prop) (t : _115095 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (_66983 : _115095) : (term563 _115095 _115098 s t f x _66983) = (term555 _115095 _115098 s t f x _66983).
Proof. exact (eq_refl (term563 _115095 _115098 s t f x _66983)). Qed.
Lemma lem5130647 {_115095 _115098 : Type'} (_66983 : _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term555 _115095 _115098 s t f x _66983.
Proof. exact (EQ_MP (@lem5130646 _115095 _115098 s t f x _66983) (@lem5130645 _115095 _115098 _66983 y' t s f x h1)). Qed.
Lemma lem5130663 {_115095 _115098 : Type'} (_66979 : _115098 -> _115095) (_66980 : _115098) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term503 _115095 _115098 s y' _66979 _66980.
Proof. exact (proj2 (@lem5130638 _115095 _115098 _66979 _66980 g y t s y' h1)). Qed.
Lemma lem5130669 {_115095 _115098 : Type'} (_66978 : _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term564 _115095 _115098 t y _66978 s.
Proof. exact (proj1 (@lem5130632 _115095 _115098 _66978 g y t s y' h1)). Qed.
Lemma lem5130675 {_115095 _115098 : Type'} (_66978 : _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term565 _115095 _115098 t g y _66978.
Proof. exact (proj2 (@lem5130632 _115095 _115098 _66978 g y t s y' h1)). Qed.
Lemma lem5130681 {_115095 _115098 : Type'} (_66983 : _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term564 _115095 _115098 t x _66983 s.
Proof. exact (proj1 (@lem5130647 _115095 _115098 _66983 y' t s f x h1)). Qed.
Lemma lem5130687 {_115095 _115098 : Type'} (_66983 : _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term566 _115095 _115098 t f x _66983.
Proof. exact (proj2 (@lem5130647 _115095 _115098 _66983 y' t s f x h1)). Qed.
Lemma lem5130695 {_115095 _115098 : Type'} (_66982 : _115098) (_66981 : _115098 -> _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term479 _115095 _115098 s _66982 y' _66981.
Proof. exact (proj2 (@lem5130644 _115095 _115098 _66982 _66981 y' t s f x h1)). Qed.
Lemma lem5130814 {_115095 : Type'} (x : _115095) (y : _115095) (z : _115095) : term567 _115095 x y z.
Proof. exact (@lem21385 _115095 x y z). Qed.
Lemma lem5130832 {_115095 _115098 : Type'} (_66979 : _115098 -> _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term490 _115095 _115098 y' _66979 t.
Proof. exact (proj1 (@lem5130638 _115095 _115098 _66979 (@el _115098) g y t s y' h1)). Qed.
Lemma lem5130833 {_115095 _115098 : Type'} (_66979 : _115098 -> _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term490 _115095 _115098 y' _66979 t.
Proof. exact (@lem5130832 _115095 _115098 _66979 g y t s y' h1). Qed.
Lemma lem5130834 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term490 _115095 _115098 y' g t.
Proof. exact (@lem5130833 _115095 _115098 g g y t s y' h1). Qed.
Lemma lem5130835 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term568 _115095 _115098 y' g t.
Proof. exact (fun h0 : term569 _115095 _115098 y' g t => @lem5130834 _115095 _115098 g y t s y' h1). Qed.
Lemma lem5130837 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5130838 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) (t : _115095 -> Prop) : (term568 _115095 _115098 y' g t) = (term490 _115095 _115098 y' g t).
Proof. exact (@lem5130837 (term490 _115095 _115098 y' g t)). Qed.
Lemma lem5130839 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term490 _115095 _115098 y' g t.
Proof. exact (EQ_MP (@lem5130838 _115095 _115098 y' g t) (@lem5130835 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5130845 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5130846 {_115095 _115098 : Type'} (y : _115095 -> _115098) (s : _115098 -> Prop) (_66978 : _115095) (t : _115095 -> Prop) : (term564 _115095 _115098 t y _66978 s) = (term571 _115095 _115098 y s _66978 t).
Proof. exact (@lem5130845 (term463 _115095 _115098 y _66978 s) (term469 _115095 _66978 t)). Qed.
Lemma lem5130852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5130853 {_115095 _115098 : Type'} (y : _115095 -> _115098) (s : _115098 -> Prop) (_66978 : _115095) (t : _115095 -> Prop) : (term572 _115095 _115098 t y _66978 s) = (term573 _115095 _115098 y s _66978 t).
Proof. exact (MK_COMB (@lem5130852) (@lem5130846 _115095 _115098 y s _66978 t)). Qed.
Lemma lem5130859 {_115095 _115098 : Type'} (y : _115095 -> _115098) (s : _115098 -> Prop) (_66978 : _115095) (t : _115095 -> Prop) : (term571 _115095 _115098 y s _66978 t) = (term571 _115095 _115098 y s _66978 t).
Proof. exact (eq_refl (term571 _115095 _115098 y s _66978 t)). Qed.
Lemma lem5130860 {_115095 _115098 : Type'} (y : _115095 -> _115098) (s : _115098 -> Prop) (_66978 : _115095) (t : _115095 -> Prop) : ((term564 _115095 _115098 t y _66978 s) = (term571 _115095 _115098 y s _66978 t)) = ((term571 _115095 _115098 y s _66978 t) = (term571 _115095 _115098 y s _66978 t)).
Proof. exact (MK_COMB (@lem5130853 _115095 _115098 y s _66978 t) (@lem5130859 _115095 _115098 y s _66978 t)). Qed.
Lemma lem5130862 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5130863 (x : Prop) : (x = x) = True.
Proof. exact (@lem5130862 Prop x). Qed.
Lemma lem5130864 {_115095 _115098 : Type'} (y : _115095 -> _115098) (s : _115098 -> Prop) (_66978 : _115095) (t : _115095 -> Prop) : ((term571 _115095 _115098 y s _66978 t) = (term571 _115095 _115098 y s _66978 t)) = True.
Proof. exact (@lem5130863 (term571 _115095 _115098 y s _66978 t)). Qed.
Lemma lem5130865 {_115095 _115098 : Type'} (y : _115095 -> _115098) (s : _115098 -> Prop) (_66978 : _115095) (t : _115095 -> Prop) : ((term564 _115095 _115098 t y _66978 s) = (term571 _115095 _115098 y s _66978 t)) = True.
Proof. exact (TRANS (@lem5130860 _115095 _115098 y s _66978 t) (@lem5130864 _115095 _115098 y s _66978 t)). Qed.
Lemma lem5130866 {_115095 _115098 : Type'} (y : _115095 -> _115098) (s : _115098 -> Prop) (_66978 : _115095) (t : _115095 -> Prop) : True = ((term564 _115095 _115098 t y _66978 s) = (term571 _115095 _115098 y s _66978 t)).
Proof. exact (SYM (@lem5130865 _115095 _115098 y s _66978 t)). Qed.
Lemma lem5130867 {_115095 _115098 : Type'} (y : _115095 -> _115098) (s : _115098 -> Prop) (_66978 : _115095) (t : _115095 -> Prop) : (term564 _115095 _115098 t y _66978 s) = (term571 _115095 _115098 y s _66978 t).
Proof. exact (EQ_MP (@lem5130866 _115095 _115098 y s _66978 t) (@lem0)). Qed.
Lemma lem5130868 {_115095 _115098 : Type'} (_66978 : _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term571 _115095 _115098 y s _66978 t.
Proof. exact (EQ_MP (@lem5130867 _115095 _115098 y s _66978 t) (@lem5130669 _115095 _115098 _66978 g y t s y' h1)). Qed.
Lemma lem5130870 (b : Prop) (a : Prop) : (a \/ b) = (term574 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5130871 {_115095 _115098 : Type'} (t : _115095 -> Prop) (y : _115095 -> _115098) (_66978 : _115095) (s : _115098 -> Prop) : (term571 _115095 _115098 y s _66978 t) = (term575 _115095 _115098 t y _66978 s).
Proof. exact (@lem5130870 (term469 _115095 _66978 t) (term463 _115095 _115098 y _66978 s)). Qed.
Lemma lem5130873 (a : Prop) : (term25 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5130874 {_115095 : Type'} (_66978 : _115095) (t : _115095 -> Prop) : (term576 _115095 _66978 t) = (term468 _115095 _66978 t).
Proof. exact (@lem5130873 (term468 _115095 _66978 t)). Qed.
Lemma lem5130875 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5130876 {_115095 : Type'} (_66978 : _115095) (t : _115095 -> Prop) : (term577 _115095 _66978 t) = (term578 _115095 _66978 t).
Proof. exact (MK_COMB (@lem5130875) (@lem5130874 _115095 _66978 t)). Qed.
Lemma lem5130877 {_115095 _115098 : Type'} (y : _115095 -> _115098) (_66978 : _115095) (s : _115098 -> Prop) : (term463 _115095 _115098 y _66978 s) = (term463 _115095 _115098 y _66978 s).
Proof. exact (eq_refl (term463 _115095 _115098 y _66978 s)). Qed.
Lemma lem5130878 {_115095 _115098 : Type'} (t : _115095 -> Prop) (y : _115095 -> _115098) (_66978 : _115095) (s : _115098 -> Prop) : (term575 _115095 _115098 t y _66978 s) = (term579 _115095 _115098 t y _66978 s).
Proof. exact (MK_COMB (@lem5130876 _115095 _66978 t) (@lem5130877 _115095 _115098 y _66978 s)). Qed.
Lemma lem5130879 {_115095 _115098 : Type'} (t : _115095 -> Prop) (y : _115095 -> _115098) (_66978 : _115095) (s : _115098 -> Prop) : (term571 _115095 _115098 y s _66978 t) = (term579 _115095 _115098 t y _66978 s).
Proof. exact (TRANS (@lem5130871 _115095 _115098 t y _66978 s) (@lem5130878 _115095 _115098 t y _66978 s)). Qed.
Lemma lem5130882 {_115095 _115098 : Type'} (_66978 : _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term579 _115095 _115098 t y _66978 s.
Proof. exact (EQ_MP (@lem5130879 _115095 _115098 t y _66978 s) (@lem5130868 _115095 _115098 _66978 g y t s y' h1)). Qed.
Lemma lem5130883 {_115095 _115098 : Type'} (_66978 : _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term579 _115095 _115098 t y _66978 s.
Proof. exact (@lem5130882 _115095 _115098 _66978 g y t s y' h1). Qed.
Lemma lem5130884 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term580 _115095 _115098 t y y' g s.
Proof. exact (@lem5130883 _115095 _115098 (@I ((_115098 -> _115095) -> _115095) y' g) g y t s y' h1). Qed.
Lemma lem5130887 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term581 _115095 _115098 y y' g s.
Proof. exact (@lem5130884 _115095 _115098 g y t s y' h1 (@lem5130839 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5130888 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term582 _115095 _115098 y y' g s.
Proof. exact (fun h0 : term583 _115095 _115098 y y' g s => @lem5130887 _115095 _115098 g y t s y' h1). Qed.
Lemma lem5130890 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5130891 {_115095 _115098 : Type'} (y : _115095 -> _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) (s : _115098 -> Prop) : (term582 _115095 _115098 y y' g s) = (term581 _115095 _115098 y y' g s).
Proof. exact (@lem5130890 (term581 _115095 _115098 y y' g s)). Qed.
Lemma lem5130892 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term581 _115095 _115098 y y' g s.
Proof. exact (EQ_MP (@lem5130891 _115095 _115098 y y' g s) (@lem5130888 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5130894 {_115095 _115098 : Type'} (_66979 : _115098 -> _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term490 _115095 _115098 y' _66979 t.
Proof. exact (proj1 (@lem5130638 _115095 _115098 _66979 (@el _115098) g y t s y' h1)). Qed.
Lemma lem5130895 {_115095 _115098 : Type'} (_66979 : _115098 -> _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term490 _115095 _115098 y' _66979 t.
Proof. exact (@lem5130894 _115095 _115098 _66979 g y t s y' h1). Qed.
Lemma lem5130896 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term490 _115095 _115098 y' g t.
Proof. exact (@lem5130895 _115095 _115098 g g y t s y' h1). Qed.
Lemma lem5130897 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term568 _115095 _115098 y' g t.
Proof. exact (fun h0 : term569 _115095 _115098 y' g t => @lem5130896 _115095 _115098 g y t s y' h1). Qed.
Lemma lem5130899 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5130900 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (g : _115098 -> _115095) (t : _115095 -> Prop) : (term568 _115095 _115098 y' g t) = (term490 _115095 _115098 y' g t).
Proof. exact (@lem5130899 (term490 _115095 _115098 y' g t)). Qed.
Lemma lem5130901 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term490 _115095 _115098 y' g t.
Proof. exact (EQ_MP (@lem5130900 _115095 _115098 y' g t) (@lem5130897 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5130907 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5130908 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (_66978 : _115095) (t : _115095 -> Prop) : (term565 _115095 _115098 t g y _66978) = (term584 _115095 _115098 g y _66978 t).
Proof. exact (@lem5130907 ((term456 _115095 _115098 g y _66978) = _66978) (term469 _115095 _66978 t)). Qed.
Lemma lem5130916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5130917 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (_66978 : _115095) (t : _115095 -> Prop) : (term585 _115095 _115098 t g y _66978) = (term586 _115095 _115098 g y _66978 t).
Proof. exact (MK_COMB (@lem5130916) (@lem5130908 _115095 _115098 g y _66978 t)). Qed.
Lemma lem5130925 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (_66978 : _115095) (t : _115095 -> Prop) : (term584 _115095 _115098 g y _66978 t) = (term584 _115095 _115098 g y _66978 t).
Proof. exact (eq_refl (term584 _115095 _115098 g y _66978 t)). Qed.
Lemma lem5130926 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (_66978 : _115095) (t : _115095 -> Prop) : ((term565 _115095 _115098 t g y _66978) = (term584 _115095 _115098 g y _66978 t)) = ((term584 _115095 _115098 g y _66978 t) = (term584 _115095 _115098 g y _66978 t)).
Proof. exact (MK_COMB (@lem5130917 _115095 _115098 g y _66978 t) (@lem5130925 _115095 _115098 g y _66978 t)). Qed.
Lemma lem5130928 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5130929 (x : Prop) : (x = x) = True.
Proof. exact (@lem5130928 Prop x). Qed.
Lemma lem5130930 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (_66978 : _115095) (t : _115095 -> Prop) : ((term584 _115095 _115098 g y _66978 t) = (term584 _115095 _115098 g y _66978 t)) = True.
Proof. exact (@lem5130929 (term584 _115095 _115098 g y _66978 t)). Qed.
Lemma lem5130931 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (_66978 : _115095) (t : _115095 -> Prop) : ((term565 _115095 _115098 t g y _66978) = (term584 _115095 _115098 g y _66978 t)) = True.
Proof. exact (TRANS (@lem5130926 _115095 _115098 g y _66978 t) (@lem5130930 _115095 _115098 g y _66978 t)). Qed.
Lemma lem5130932 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (_66978 : _115095) (t : _115095 -> Prop) : True = ((term565 _115095 _115098 t g y _66978) = (term584 _115095 _115098 g y _66978 t)).
Proof. exact (SYM (@lem5130931 _115095 _115098 g y _66978 t)). Qed.
Lemma lem5130933 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (_66978 : _115095) (t : _115095 -> Prop) : (term565 _115095 _115098 t g y _66978) = (term584 _115095 _115098 g y _66978 t).
Proof. exact (EQ_MP (@lem5130932 _115095 _115098 g y _66978 t) (@lem0)). Qed.
Lemma lem5130934 {_115095 _115098 : Type'} (_66978 : _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term584 _115095 _115098 g y _66978 t.
Proof. exact (EQ_MP (@lem5130933 _115095 _115098 g y _66978 t) (@lem5130675 _115095 _115098 _66978 g y t s y' h1)). Qed.
Lemma lem5130936 (b : Prop) (a : Prop) : (a \/ b) = (term574 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5130937 {_115095 _115098 : Type'} (t : _115095 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) (_66978 : _115095) : (term584 _115095 _115098 g y _66978 t) = (term587 _115095 _115098 t g y _66978).
Proof. exact (@lem5130936 (term469 _115095 _66978 t) ((term456 _115095 _115098 g y _66978) = _66978)). Qed.
Lemma lem5130939 (a : Prop) : (term25 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5130940 {_115095 : Type'} (_66978 : _115095) (t : _115095 -> Prop) : (term576 _115095 _66978 t) = (term468 _115095 _66978 t).
Proof. exact (@lem5130939 (term468 _115095 _66978 t)). Qed.
Lemma lem5130941 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5130942 {_115095 : Type'} (_66978 : _115095) (t : _115095 -> Prop) : (term577 _115095 _66978 t) = (term578 _115095 _66978 t).
Proof. exact (MK_COMB (@lem5130941) (@lem5130940 _115095 _66978 t)). Qed.
Lemma lem5130943 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (_66978 : _115095) : ((term456 _115095 _115098 g y _66978) = _66978) = ((term456 _115095 _115098 g y _66978) = _66978).
Proof. exact (eq_refl ((term456 _115095 _115098 g y _66978) = _66978)). Qed.
Lemma lem5130944 {_115095 _115098 : Type'} (t : _115095 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) (_66978 : _115095) : (term587 _115095 _115098 t g y _66978) = (term588 _115095 _115098 t g y _66978).
Proof. exact (MK_COMB (@lem5130942 _115095 _66978 t) (@lem5130943 _115095 _115098 g y _66978)). Qed.
Lemma lem5130945 {_115095 _115098 : Type'} (t : _115095 -> Prop) (g : _115098 -> _115095) (y : _115095 -> _115098) (_66978 : _115095) : (term584 _115095 _115098 g y _66978 t) = (term588 _115095 _115098 t g y _66978).
Proof. exact (TRANS (@lem5130937 _115095 _115098 t g y _66978) (@lem5130944 _115095 _115098 t g y _66978)). Qed.
Lemma lem5130948 {_115095 _115098 : Type'} (_66978 : _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term588 _115095 _115098 t g y _66978.
Proof. exact (EQ_MP (@lem5130945 _115095 _115098 t g y _66978) (@lem5130934 _115095 _115098 _66978 g y t s y' h1)). Qed.
Lemma lem5130949 {_115095 _115098 : Type'} (_66978 : _115095) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term588 _115095 _115098 t g y _66978.
Proof. exact (@lem5130948 _115095 _115098 _66978 g y t s y' h1). Qed.
Lemma lem5130950 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term589 _115095 _115098 t y y' g.
Proof. exact (@lem5130949 _115095 _115098 (@I ((_115098 -> _115095) -> _115095) y' g) g y t s y' h1). Qed.
Lemma lem5130953 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : (term590 _115095 _115098 y y' g) = (@I ((_115098 -> _115095) -> _115095) y' g).
Proof. exact (@lem5130950 _115095 _115098 g y t s y' h1 (@lem5130901 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5130954 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term591 _115095 _115098 y y' g.
Proof. exact (fun h0 : term592 _115095 _115098 y y' g => @lem5130953 _115095 _115098 g y t s y' h1). Qed.
Lemma lem5130956 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5130957 {_115095 _115098 : Type'} (y : _115095 -> _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term591 _115095 _115098 y y' g) = ((term590 _115095 _115098 y y' g) = (@I ((_115098 -> _115095) -> _115095) y' g)).
Proof. exact (@lem5130956 ((term590 _115095 _115098 y y' g) = (@I ((_115098 -> _115095) -> _115095) y' g))). Qed.
Lemma lem5130958 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : (term590 _115095 _115098 y y' g) = (@I ((_115098 -> _115095) -> _115095) y' g).
Proof. exact (EQ_MP (@lem5130957 _115095 _115098 y y' g) (@lem5130954 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5130960 {_115095 : Type'} (x : _115095) : x = x.
Proof. exact (@lem21386 _115095 x). Qed.
Lemma lem5130961 {_115095 : Type'} (x : _115095) : x = x.
Proof. exact (@lem5130960 _115095 x). Qed.
Lemma lem5130962 {_115095 _115098 : Type'} (y : _115095 -> _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term590 _115095 _115098 y y' g) = (term590 _115095 _115098 y y' g).
Proof. exact (@lem5130961 _115095 (term590 _115095 _115098 y y' g)). Qed.
Lemma lem5130963 {_115095 _115098 : Type'} (y : _115095 -> _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : term593 _115095 _115098 y y' g.
Proof. exact (fun h0 : term594 _115095 _115098 y y' g => @lem5130962 _115095 _115098 y y' g). Qed.
Lemma lem5130965 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5130966 {_115095 _115098 : Type'} (y : _115095 -> _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term593 _115095 _115098 y y' g) = ((term590 _115095 _115098 y y' g) = (term590 _115095 _115098 y y' g)).
Proof. exact (@lem5130965 ((term590 _115095 _115098 y y' g) = (term590 _115095 _115098 y y' g))). Qed.
Lemma lem5130967 {_115095 _115098 : Type'} (y : _115095 -> _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term590 _115095 _115098 y y' g) = (term590 _115095 _115098 y y' g).
Proof. exact (EQ_MP (@lem5130966 _115095 _115098 y y' g) (@lem5130963 _115095 _115098 y y' g)). Qed.
Lemma lem5130985 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5130986 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term595 _115095 x y z) = (term596 _115095 y x z).
Proof. exact (@lem5130985 (y = z) (term597 _115095 x z)). Qed.
Lemma lem5130996 {_115095 : Type'} (x : _115095) (y : _115095) : (term598 _115095 x y) = (term598 _115095 x y).
Proof. exact (eq_refl (term598 _115095 x y)). Qed.
Lemma lem5130997 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term567 _115095 x y z) = (term599 _115095 y x z).
Proof. exact (MK_COMB (@lem5130996 _115095 x y) (@lem5130986 _115095 y x z)). Qed.
Lemma lem5131001 (q : Prop) (p : Prop) (r : Prop) : (term600 p q r) = (term600 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5131002 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term599 _115095 y x z) = (term601 _115095 y x z).
Proof. exact (@lem5131001 (y = z) (term597 _115095 x y) (term597 _115095 x z)). Qed.
Lemma lem5131024 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term567 _115095 x y z) = (term601 _115095 y x z).
Proof. exact (TRANS (@lem5130997 _115095 y x z) (@lem5131002 _115095 y x z)). Qed.
Lemma lem5131025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5131026 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term602 _115095 x y z) = (term603 _115095 y x z).
Proof. exact (MK_COMB (@lem5131025) (@lem5131024 _115095 y x z)). Qed.
Lemma lem5131048 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term601 _115095 y x z) = (term601 _115095 y x z).
Proof. exact (eq_refl (term601 _115095 y x z)). Qed.
Lemma lem5131049 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : ((term567 _115095 x y z) = (term601 _115095 y x z)) = ((term601 _115095 y x z) = (term601 _115095 y x z)).
Proof. exact (MK_COMB (@lem5131026 _115095 y x z) (@lem5131048 _115095 y x z)). Qed.
Lemma lem5131051 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5131052 (x : Prop) : (x = x) = True.
Proof. exact (@lem5131051 Prop x). Qed.
Lemma lem5131053 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : ((term601 _115095 y x z) = (term601 _115095 y x z)) = True.
Proof. exact (@lem5131052 (term601 _115095 y x z)). Qed.
Lemma lem5131054 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : ((term567 _115095 x y z) = (term601 _115095 y x z)) = True.
Proof. exact (TRANS (@lem5131049 _115095 y x z) (@lem5131053 _115095 y x z)). Qed.
Lemma lem5131055 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : True = ((term567 _115095 x y z) = (term601 _115095 y x z)).
Proof. exact (SYM (@lem5131054 _115095 y x z)). Qed.
Lemma lem5131056 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term567 _115095 x y z) = (term601 _115095 y x z).
Proof. exact (EQ_MP (@lem5131055 _115095 y x z) (@lem0)). Qed.
Lemma lem5131057 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : term601 _115095 y x z.
Proof. exact (EQ_MP (@lem5131056 _115095 y x z) (@lem5130814 _115095 x y z)). Qed.
Lemma lem5131059 (b : Prop) (a : Prop) : (a \/ b) = (term574 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5131060 {_115095 : Type'} (x : _115095) (y : _115095) (z : _115095) : (term601 _115095 y x z) = (term604 _115095 x y z).
Proof. exact (@lem5131059 (term605 _115095 y x z) (y = z)). Qed.
Lemma lem5131062 (a : Prop) (b : Prop) : (term606 a b) = (term607 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5131063 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term608 _115095 y x z) = (term609 _115095 y x z).
Proof. exact (@lem5131062 (term597 _115095 x y) (term597 _115095 x z)). Qed.
Lemma lem5131065 (a : Prop) : (term25 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5131066 {_115095 : Type'} (x : _115095) (y : _115095) : (term610 _115095 x y) = (x = y).
Proof. exact (@lem5131065 (x = y)). Qed.
Lemma lem5131067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5131068 {_115095 : Type'} (x : _115095) (y : _115095) : (term611 _115095 x y) = (term612 _115095 x y).
Proof. exact (MK_COMB (@lem5131067) (@lem5131066 _115095 x y)). Qed.
Lemma lem5131070 (a : Prop) : (term25 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5131071 {_115095 : Type'} (x : _115095) (z : _115095) : (term610 _115095 x z) = (x = z).
Proof. exact (@lem5131070 (x = z)). Qed.
Lemma lem5131072 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term609 _115095 y x z) = (term613 _115095 y x z).
Proof. exact (MK_COMB (@lem5131068 _115095 x y) (@lem5131071 _115095 x z)). Qed.
Lemma lem5131073 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term608 _115095 y x z) = (term613 _115095 y x z).
Proof. exact (TRANS (@lem5131063 _115095 y x z) (@lem5131072 _115095 y x z)). Qed.
Lemma lem5131074 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5131075 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term614 _115095 y x z) = (term615 _115095 y x z).
Proof. exact (MK_COMB (@lem5131074) (@lem5131073 _115095 y x z)). Qed.
Lemma lem5131076 {_115095 : Type'} (y : _115095) (z : _115095) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5131077 {_115095 : Type'} (x : _115095) (y : _115095) (z : _115095) : (term604 _115095 x y z) = (term616 _115095 x y z).
Proof. exact (MK_COMB (@lem5131075 _115095 y x z) (@lem5131076 _115095 y z)). Qed.
Lemma lem5131078 {_115095 : Type'} (x : _115095) (y : _115095) (z : _115095) : (term601 _115095 y x z) = (term616 _115095 x y z).
Proof. exact (TRANS (@lem5131060 _115095 x y z) (@lem5131077 _115095 x y z)). Qed.
Lemma lem5131080 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term617 _115095 _115098 y y' g.
Proof. exact (conj (@lem5130958 _115095 _115098 g y t s y' h1) (@lem5130967 _115095 _115098 y y' g)). Qed.
Lemma lem5131082 {_115095 : Type'} (x : _115095) (y : _115095) (z : _115095) : term616 _115095 x y z.
Proof. exact (EQ_MP (@lem5131078 _115095 x y z) (@lem5131057 _115095 y x z)). Qed.
Lemma lem5131083 {_115095 : Type'} (x : _115095) (y : _115095) (z : _115095) : term616 _115095 x y z.
Proof. exact (@lem5131082 _115095 x y z). Qed.
Lemma lem5131084 {_115095 _115098 : Type'} (y : _115095 -> _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : term618 _115095 _115098 y y' g.
Proof. exact (@lem5131083 _115095 (term590 _115095 _115098 y y' g) (@I ((_115098 -> _115095) -> _115095) y' g) (term590 _115095 _115098 y y' g)). Qed.
Lemma lem5131087 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : (@I ((_115098 -> _115095) -> _115095) y' g) = (term590 _115095 _115098 y y' g).
Proof. exact (@lem5131084 _115095 _115098 y y' g (@lem5131080 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5131088 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term619 _115095 _115098 y y' g.
Proof. exact (fun h0 : term620 _115095 _115098 y y' g => @lem5131087 _115095 _115098 g y t s y' h1). Qed.
Lemma lem5131090 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5131091 {_115095 _115098 : Type'} (y : _115095 -> _115098) (y' : type802 _115095 _115098) (g : _115098 -> _115095) : (term619 _115095 _115098 y y' g) = ((@I ((_115098 -> _115095) -> _115095) y' g) = (term590 _115095 _115098 y y' g)).
Proof. exact (@lem5131090 ((@I ((_115098 -> _115095) -> _115095) y' g) = (term590 _115095 _115098 y y' g))). Qed.
Lemma lem5131092 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : (@I ((_115098 -> _115095) -> _115095) y' g) = (term590 _115095 _115098 y y' g).
Proof. exact (EQ_MP (@lem5131091 _115095 _115098 y y' g) (@lem5131088 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5131094 (a : Prop) (b : Prop) : (term621 a b) = (term622 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5131095 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (_66979 : _115098 -> _115095) (_66980 : _115098) : (term503 _115095 _115098 s y' _66979 _66980) = (term623 _115095 _115098 s y' _66979 _66980).
Proof. exact (@lem5131094 (term468 _115098 _66980 s) ((@I ((_115098 -> _115095) -> _115095) y' _66979) = (@I (_115098 -> _115095) _66979 _66980))). Qed.
Lemma lem5131097 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5131098 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (_66979 : _115098 -> _115095) (_66980 : _115098) : (term623 _115095 _115098 s y' _66979 _66980) = (term624 _115095 _115098 s y' _66979 _66980).
Proof. exact (@lem5131097 (term625 _115095 _115098 s y' _66979 _66980)). Qed.
Lemma lem5131099 {_115095 _115098 : Type'} (s : _115098 -> Prop) (y' : type802 _115095 _115098) (_66979 : _115098 -> _115095) (_66980 : _115098) : (term503 _115095 _115098 s y' _66979 _66980) = (term624 _115095 _115098 s y' _66979 _66980).
Proof. exact (TRANS (@lem5131095 _115095 _115098 s y' _66979 _66980) (@lem5131098 _115095 _115098 s y' _66979 _66980)). Qed.
Lemma lem5131101 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term626 _115095 _115098 s y y' g.
Proof. exact (conj (@lem5130892 _115095 _115098 g y t s y' h1) (@lem5131092 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5131103 {_115095 _115098 : Type'} (_66979 : _115098 -> _115095) (_66980 : _115098) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term624 _115095 _115098 s y' _66979 _66980.
Proof. exact (EQ_MP (@lem5131099 _115095 _115098 s y' _66979 _66980) (@lem5130663 _115095 _115098 _66979 _66980 g y t s y' h1)). Qed.
Lemma lem5131104 {_115095 _115098 : Type'} (_66979 : _115098 -> _115095) (_66980 : _115098) (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term624 _115095 _115098 s y' _66979 _66980.
Proof. exact (@lem5131103 _115095 _115098 _66979 _66980 g y t s y' h1). Qed.
Lemma lem5131105 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term627 _115095 _115098 s y y' g.
Proof. exact (@lem5131104 _115095 _115098 g (term628 _115095 _115098 y y' g) g y t s y' h1). Qed.
Lemma lem5131108 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : False.
Proof. exact (@lem5131105 _115095 _115098 g y t s y' h1 (@lem5131101 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5131109 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : term629.
Proof. exact (fun h0 : ~ False => @lem5131108 _115095 _115098 g y t s y' h1). Qed.
Lemma lem5131111 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5131112 : term629 = False.
Proof. exact (@lem5131111 False). Qed.
Lemma lem5131113 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (y' : type802 _115095 _115098) (h1 : term519 _115095 _115098 g y t s y') : False.
Proof. exact (EQ_MP (@lem5131112) (@lem5131109 _115095 _115098 g y t s y' h1)). Qed.
Lemma lem5131236 {_115095 : Type'} (x : _115095) (y : _115095) (z : _115095) : term567 _115095 x y z.
Proof. exact (@lem21385 _115095 x y z). Qed.
Lemma lem5131250 {_115095 _115098 : Type'} (_66981 : _115098 -> _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term490 _115095 _115098 y' _66981 t.
Proof. exact (proj1 (@lem5130644 _115095 _115098 (@el _115098) _66981 y' t s f x h1)). Qed.
Lemma lem5131251 {_115095 _115098 : Type'} (_66981 : _115098 -> _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term490 _115095 _115098 y' _66981 t.
Proof. exact (@lem5131250 _115095 _115098 _66981 y' t s f x h1). Qed.
Lemma lem5131252 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term490 _115095 _115098 y' f t.
Proof. exact (@lem5131251 _115095 _115098 f y' t s f x h1). Qed.
Lemma lem5131253 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term568 _115095 _115098 y' f t.
Proof. exact (fun h0 : term569 _115095 _115098 y' f t => @lem5131252 _115095 _115098 y' t s f x h1). Qed.
Lemma lem5131255 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5131256 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) (t : _115095 -> Prop) : (term568 _115095 _115098 y' f t) = (term490 _115095 _115098 y' f t).
Proof. exact (@lem5131255 (term490 _115095 _115098 y' f t)). Qed.
Lemma lem5131257 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term490 _115095 _115098 y' f t.
Proof. exact (EQ_MP (@lem5131256 _115095 _115098 y' f t) (@lem5131253 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5131263 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5131264 {_115095 _115098 : Type'} (x : _115095 -> _115098) (s : _115098 -> Prop) (_66983 : _115095) (t : _115095 -> Prop) : (term564 _115095 _115098 t x _66983 s) = (term571 _115095 _115098 x s _66983 t).
Proof. exact (@lem5131263 (term463 _115095 _115098 x _66983 s) (term469 _115095 _66983 t)). Qed.
Lemma lem5131270 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5131271 {_115095 _115098 : Type'} (x : _115095 -> _115098) (s : _115098 -> Prop) (_66983 : _115095) (t : _115095 -> Prop) : (term572 _115095 _115098 t x _66983 s) = (term573 _115095 _115098 x s _66983 t).
Proof. exact (MK_COMB (@lem5131270) (@lem5131264 _115095 _115098 x s _66983 t)). Qed.
Lemma lem5131277 {_115095 _115098 : Type'} (x : _115095 -> _115098) (s : _115098 -> Prop) (_66983 : _115095) (t : _115095 -> Prop) : (term571 _115095 _115098 x s _66983 t) = (term571 _115095 _115098 x s _66983 t).
Proof. exact (eq_refl (term571 _115095 _115098 x s _66983 t)). Qed.
Lemma lem5131278 {_115095 _115098 : Type'} (x : _115095 -> _115098) (s : _115098 -> Prop) (_66983 : _115095) (t : _115095 -> Prop) : ((term564 _115095 _115098 t x _66983 s) = (term571 _115095 _115098 x s _66983 t)) = ((term571 _115095 _115098 x s _66983 t) = (term571 _115095 _115098 x s _66983 t)).
Proof. exact (MK_COMB (@lem5131271 _115095 _115098 x s _66983 t) (@lem5131277 _115095 _115098 x s _66983 t)). Qed.
Lemma lem5131280 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5131281 (x : Prop) : (x = x) = True.
Proof. exact (@lem5131280 Prop x). Qed.
Lemma lem5131282 {_115095 _115098 : Type'} (x : _115095 -> _115098) (s : _115098 -> Prop) (_66983 : _115095) (t : _115095 -> Prop) : ((term571 _115095 _115098 x s _66983 t) = (term571 _115095 _115098 x s _66983 t)) = True.
Proof. exact (@lem5131281 (term571 _115095 _115098 x s _66983 t)). Qed.
Lemma lem5131283 {_115095 _115098 : Type'} (x : _115095 -> _115098) (s : _115098 -> Prop) (_66983 : _115095) (t : _115095 -> Prop) : ((term564 _115095 _115098 t x _66983 s) = (term571 _115095 _115098 x s _66983 t)) = True.
Proof. exact (TRANS (@lem5131278 _115095 _115098 x s _66983 t) (@lem5131282 _115095 _115098 x s _66983 t)). Qed.
Lemma lem5131284 {_115095 _115098 : Type'} (x : _115095 -> _115098) (s : _115098 -> Prop) (_66983 : _115095) (t : _115095 -> Prop) : True = ((term564 _115095 _115098 t x _66983 s) = (term571 _115095 _115098 x s _66983 t)).
Proof. exact (SYM (@lem5131283 _115095 _115098 x s _66983 t)). Qed.
Lemma lem5131285 {_115095 _115098 : Type'} (x : _115095 -> _115098) (s : _115098 -> Prop) (_66983 : _115095) (t : _115095 -> Prop) : (term564 _115095 _115098 t x _66983 s) = (term571 _115095 _115098 x s _66983 t).
Proof. exact (EQ_MP (@lem5131284 _115095 _115098 x s _66983 t) (@lem0)). Qed.
Lemma lem5131286 {_115095 _115098 : Type'} (_66983 : _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term571 _115095 _115098 x s _66983 t.
Proof. exact (EQ_MP (@lem5131285 _115095 _115098 x s _66983 t) (@lem5130681 _115095 _115098 _66983 y' t s f x h1)). Qed.
Lemma lem5131288 (b : Prop) (a : Prop) : (a \/ b) = (term574 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5131289 {_115095 _115098 : Type'} (t : _115095 -> Prop) (x : _115095 -> _115098) (_66983 : _115095) (s : _115098 -> Prop) : (term571 _115095 _115098 x s _66983 t) = (term575 _115095 _115098 t x _66983 s).
Proof. exact (@lem5131288 (term469 _115095 _66983 t) (term463 _115095 _115098 x _66983 s)). Qed.
Lemma lem5131291 (a : Prop) : (term25 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5131292 {_115095 : Type'} (_66983 : _115095) (t : _115095 -> Prop) : (term576 _115095 _66983 t) = (term468 _115095 _66983 t).
Proof. exact (@lem5131291 (term468 _115095 _66983 t)). Qed.
Lemma lem5131293 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5131294 {_115095 : Type'} (_66983 : _115095) (t : _115095 -> Prop) : (term577 _115095 _66983 t) = (term578 _115095 _66983 t).
Proof. exact (MK_COMB (@lem5131293) (@lem5131292 _115095 _66983 t)). Qed.
Lemma lem5131295 {_115095 _115098 : Type'} (x : _115095 -> _115098) (_66983 : _115095) (s : _115098 -> Prop) : (term463 _115095 _115098 x _66983 s) = (term463 _115095 _115098 x _66983 s).
Proof. exact (eq_refl (term463 _115095 _115098 x _66983 s)). Qed.
Lemma lem5131296 {_115095 _115098 : Type'} (t : _115095 -> Prop) (x : _115095 -> _115098) (_66983 : _115095) (s : _115098 -> Prop) : (term575 _115095 _115098 t x _66983 s) = (term579 _115095 _115098 t x _66983 s).
Proof. exact (MK_COMB (@lem5131294 _115095 _66983 t) (@lem5131295 _115095 _115098 x _66983 s)). Qed.
Lemma lem5131297 {_115095 _115098 : Type'} (t : _115095 -> Prop) (x : _115095 -> _115098) (_66983 : _115095) (s : _115098 -> Prop) : (term571 _115095 _115098 x s _66983 t) = (term579 _115095 _115098 t x _66983 s).
Proof. exact (TRANS (@lem5131289 _115095 _115098 t x _66983 s) (@lem5131296 _115095 _115098 t x _66983 s)). Qed.
Lemma lem5131300 {_115095 _115098 : Type'} (_66983 : _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term579 _115095 _115098 t x _66983 s.
Proof. exact (EQ_MP (@lem5131297 _115095 _115098 t x _66983 s) (@lem5131286 _115095 _115098 _66983 y' t s f x h1)). Qed.
Lemma lem5131301 {_115095 _115098 : Type'} (_66983 : _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term579 _115095 _115098 t x _66983 s.
Proof. exact (@lem5131300 _115095 _115098 _66983 y' t s f x h1). Qed.
Lemma lem5131302 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term580 _115095 _115098 t x y' f s.
Proof. exact (@lem5131301 _115095 _115098 (@I ((_115098 -> _115095) -> _115095) y' f) y' t s f x h1). Qed.
Lemma lem5131305 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term581 _115095 _115098 x y' f s.
Proof. exact (@lem5131302 _115095 _115098 y' t s f x h1 (@lem5131257 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5131306 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term582 _115095 _115098 x y' f s.
Proof. exact (fun h0 : term583 _115095 _115098 x y' f s => @lem5131305 _115095 _115098 y' t s f x h1). Qed.
Lemma lem5131308 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5131309 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y' : type802 _115095 _115098) (f : _115098 -> _115095) (s : _115098 -> Prop) : (term582 _115095 _115098 x y' f s) = (term581 _115095 _115098 x y' f s).
Proof. exact (@lem5131308 (term581 _115095 _115098 x y' f s)). Qed.
Lemma lem5131310 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term581 _115095 _115098 x y' f s.
Proof. exact (EQ_MP (@lem5131309 _115095 _115098 x y' f s) (@lem5131306 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5131312 {_115095 _115098 : Type'} (_66981 : _115098 -> _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term490 _115095 _115098 y' _66981 t.
Proof. exact (proj1 (@lem5130644 _115095 _115098 (@el _115098) _66981 y' t s f x h1)). Qed.
Lemma lem5131313 {_115095 _115098 : Type'} (_66981 : _115098 -> _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term490 _115095 _115098 y' _66981 t.
Proof. exact (@lem5131312 _115095 _115098 _66981 y' t s f x h1). Qed.
Lemma lem5131314 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term490 _115095 _115098 y' f t.
Proof. exact (@lem5131313 _115095 _115098 f y' t s f x h1). Qed.
Lemma lem5131315 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term568 _115095 _115098 y' f t.
Proof. exact (fun h0 : term569 _115095 _115098 y' f t => @lem5131314 _115095 _115098 y' t s f x h1). Qed.
Lemma lem5131317 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5131318 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) (t : _115095 -> Prop) : (term568 _115095 _115098 y' f t) = (term490 _115095 _115098 y' f t).
Proof. exact (@lem5131317 (term490 _115095 _115098 y' f t)). Qed.
Lemma lem5131319 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term490 _115095 _115098 y' f t.
Proof. exact (EQ_MP (@lem5131318 _115095 _115098 y' f t) (@lem5131315 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5131325 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5131326 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115095 -> _115098) (_66983 : _115095) (t : _115095 -> Prop) : (term566 _115095 _115098 t f x _66983) = (term630 _115095 _115098 f x _66983 t).
Proof. exact (@lem5131325 (_66983 = (term456 _115095 _115098 f x _66983)) (term469 _115095 _66983 t)). Qed.
Lemma lem5131334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5131335 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115095 -> _115098) (_66983 : _115095) (t : _115095 -> Prop) : (term631 _115095 _115098 t f x _66983) = (term632 _115095 _115098 f x _66983 t).
Proof. exact (MK_COMB (@lem5131334) (@lem5131326 _115095 _115098 f x _66983 t)). Qed.
Lemma lem5131343 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115095 -> _115098) (_66983 : _115095) (t : _115095 -> Prop) : (term630 _115095 _115098 f x _66983 t) = (term630 _115095 _115098 f x _66983 t).
Proof. exact (eq_refl (term630 _115095 _115098 f x _66983 t)). Qed.
Lemma lem5131344 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115095 -> _115098) (_66983 : _115095) (t : _115095 -> Prop) : ((term566 _115095 _115098 t f x _66983) = (term630 _115095 _115098 f x _66983 t)) = ((term630 _115095 _115098 f x _66983 t) = (term630 _115095 _115098 f x _66983 t)).
Proof. exact (MK_COMB (@lem5131335 _115095 _115098 f x _66983 t) (@lem5131343 _115095 _115098 f x _66983 t)). Qed.
Lemma lem5131346 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5131347 (x : Prop) : (x = x) = True.
Proof. exact (@lem5131346 Prop x). Qed.
Lemma lem5131348 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115095 -> _115098) (_66983 : _115095) (t : _115095 -> Prop) : ((term630 _115095 _115098 f x _66983 t) = (term630 _115095 _115098 f x _66983 t)) = True.
Proof. exact (@lem5131347 (term630 _115095 _115098 f x _66983 t)). Qed.
Lemma lem5131349 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115095 -> _115098) (_66983 : _115095) (t : _115095 -> Prop) : ((term566 _115095 _115098 t f x _66983) = (term630 _115095 _115098 f x _66983 t)) = True.
Proof. exact (TRANS (@lem5131344 _115095 _115098 f x _66983 t) (@lem5131348 _115095 _115098 f x _66983 t)). Qed.
Lemma lem5131350 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115095 -> _115098) (_66983 : _115095) (t : _115095 -> Prop) : True = ((term566 _115095 _115098 t f x _66983) = (term630 _115095 _115098 f x _66983 t)).
Proof. exact (SYM (@lem5131349 _115095 _115098 f x _66983 t)). Qed.
Lemma lem5131351 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115095 -> _115098) (_66983 : _115095) (t : _115095 -> Prop) : (term566 _115095 _115098 t f x _66983) = (term630 _115095 _115098 f x _66983 t).
Proof. exact (EQ_MP (@lem5131350 _115095 _115098 f x _66983 t) (@lem0)). Qed.
Lemma lem5131352 {_115095 _115098 : Type'} (_66983 : _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term630 _115095 _115098 f x _66983 t.
Proof. exact (EQ_MP (@lem5131351 _115095 _115098 f x _66983 t) (@lem5130687 _115095 _115098 _66983 y' t s f x h1)). Qed.
Lemma lem5131354 (b : Prop) (a : Prop) : (a \/ b) = (term574 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5131355 {_115095 _115098 : Type'} (t : _115095 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (_66983 : _115095) : (term630 _115095 _115098 f x _66983 t) = (term633 _115095 _115098 t f x _66983).
Proof. exact (@lem5131354 (term469 _115095 _66983 t) (_66983 = (term456 _115095 _115098 f x _66983))). Qed.
Lemma lem5131357 (a : Prop) : (term25 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5131358 {_115095 : Type'} (_66983 : _115095) (t : _115095 -> Prop) : (term576 _115095 _66983 t) = (term468 _115095 _66983 t).
Proof. exact (@lem5131357 (term468 _115095 _66983 t)). Qed.
Lemma lem5131359 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5131360 {_115095 : Type'} (_66983 : _115095) (t : _115095 -> Prop) : (term577 _115095 _66983 t) = (term578 _115095 _66983 t).
Proof. exact (MK_COMB (@lem5131359) (@lem5131358 _115095 _66983 t)). Qed.
Lemma lem5131361 {_115095 _115098 : Type'} (f : _115098 -> _115095) (x : _115095 -> _115098) (_66983 : _115095) : (_66983 = (term456 _115095 _115098 f x _66983)) = (_66983 = (term456 _115095 _115098 f x _66983)).
Proof. exact (eq_refl (_66983 = (term456 _115095 _115098 f x _66983))). Qed.
Lemma lem5131362 {_115095 _115098 : Type'} (t : _115095 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (_66983 : _115095) : (term633 _115095 _115098 t f x _66983) = (term634 _115095 _115098 t f x _66983).
Proof. exact (MK_COMB (@lem5131360 _115095 _66983 t) (@lem5131361 _115095 _115098 f x _66983)). Qed.
Lemma lem5131363 {_115095 _115098 : Type'} (t : _115095 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (_66983 : _115095) : (term630 _115095 _115098 f x _66983 t) = (term634 _115095 _115098 t f x _66983).
Proof. exact (TRANS (@lem5131355 _115095 _115098 t f x _66983) (@lem5131362 _115095 _115098 t f x _66983)). Qed.
Lemma lem5131366 {_115095 _115098 : Type'} (_66983 : _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term634 _115095 _115098 t f x _66983.
Proof. exact (EQ_MP (@lem5131363 _115095 _115098 t f x _66983) (@lem5131352 _115095 _115098 _66983 y' t s f x h1)). Qed.
Lemma lem5131367 {_115095 _115098 : Type'} (_66983 : _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term634 _115095 _115098 t f x _66983.
Proof. exact (@lem5131366 _115095 _115098 _66983 y' t s f x h1). Qed.
Lemma lem5131368 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term635 _115095 _115098 t x y' f.
Proof. exact (@lem5131367 _115095 _115098 (@I ((_115098 -> _115095) -> _115095) y' f) y' t s f x h1). Qed.
Lemma lem5131371 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : (@I ((_115098 -> _115095) -> _115095) y' f) = (term590 _115095 _115098 x y' f).
Proof. exact (@lem5131368 _115095 _115098 y' t s f x h1 (@lem5131319 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5131372 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term619 _115095 _115098 x y' f.
Proof. exact (fun h0 : term620 _115095 _115098 x y' f => @lem5131371 _115095 _115098 y' t s f x h1). Qed.
Lemma lem5131374 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5131375 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term619 _115095 _115098 x y' f) = ((@I ((_115098 -> _115095) -> _115095) y' f) = (term590 _115095 _115098 x y' f)).
Proof. exact (@lem5131374 ((@I ((_115098 -> _115095) -> _115095) y' f) = (term590 _115095 _115098 x y' f))). Qed.
Lemma lem5131376 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : (@I ((_115098 -> _115095) -> _115095) y' f) = (term590 _115095 _115098 x y' f).
Proof. exact (EQ_MP (@lem5131375 _115095 _115098 x y' f) (@lem5131372 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5131378 {_115095 : Type'} (x : _115095) : x = x.
Proof. exact (@lem21386 _115095 x). Qed.
Lemma lem5131379 {_115095 : Type'} (x : _115095) : x = x.
Proof. exact (@lem5131378 _115095 x). Qed.
Lemma lem5131380 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (@I ((_115098 -> _115095) -> _115095) y' f) = (@I ((_115098 -> _115095) -> _115095) y' f).
Proof. exact (@lem5131379 _115095 (@I ((_115098 -> _115095) -> _115095) y' f)). Qed.
Lemma lem5131381 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) : term636 _115095 _115098 y' f.
Proof. exact (fun h0 : term637 _115095 _115098 y' f => @lem5131380 _115095 _115098 y' f). Qed.
Lemma lem5131383 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5131384 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term636 _115095 _115098 y' f) = ((@I ((_115098 -> _115095) -> _115095) y' f) = (@I ((_115098 -> _115095) -> _115095) y' f)).
Proof. exact (@lem5131383 ((@I ((_115098 -> _115095) -> _115095) y' f) = (@I ((_115098 -> _115095) -> _115095) y' f))). Qed.
Lemma lem5131385 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (@I ((_115098 -> _115095) -> _115095) y' f) = (@I ((_115098 -> _115095) -> _115095) y' f).
Proof. exact (EQ_MP (@lem5131384 _115095 _115098 y' f) (@lem5131381 _115095 _115098 y' f)). Qed.
Lemma lem5131403 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5131404 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term595 _115095 x y z) = (term596 _115095 y x z).
Proof. exact (@lem5131403 (y = z) (term597 _115095 x z)). Qed.
Lemma lem5131414 {_115095 : Type'} (x : _115095) (y : _115095) : (term598 _115095 x y) = (term598 _115095 x y).
Proof. exact (eq_refl (term598 _115095 x y)). Qed.
Lemma lem5131415 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term567 _115095 x y z) = (term599 _115095 y x z).
Proof. exact (MK_COMB (@lem5131414 _115095 x y) (@lem5131404 _115095 y x z)). Qed.
Lemma lem5131419 (q : Prop) (p : Prop) (r : Prop) : (term600 p q r) = (term600 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5131420 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term599 _115095 y x z) = (term601 _115095 y x z).
Proof. exact (@lem5131419 (y = z) (term597 _115095 x y) (term597 _115095 x z)). Qed.
Lemma lem5131442 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term567 _115095 x y z) = (term601 _115095 y x z).
Proof. exact (TRANS (@lem5131415 _115095 y x z) (@lem5131420 _115095 y x z)). Qed.
Lemma lem5131443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5131444 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term602 _115095 x y z) = (term603 _115095 y x z).
Proof. exact (MK_COMB (@lem5131443) (@lem5131442 _115095 y x z)). Qed.
Lemma lem5131466 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term601 _115095 y x z) = (term601 _115095 y x z).
Proof. exact (eq_refl (term601 _115095 y x z)). Qed.
Lemma lem5131467 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : ((term567 _115095 x y z) = (term601 _115095 y x z)) = ((term601 _115095 y x z) = (term601 _115095 y x z)).
Proof. exact (MK_COMB (@lem5131444 _115095 y x z) (@lem5131466 _115095 y x z)). Qed.
Lemma lem5131469 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5131470 (x : Prop) : (x = x) = True.
Proof. exact (@lem5131469 Prop x). Qed.
Lemma lem5131471 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : ((term601 _115095 y x z) = (term601 _115095 y x z)) = True.
Proof. exact (@lem5131470 (term601 _115095 y x z)). Qed.
Lemma lem5131472 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : ((term567 _115095 x y z) = (term601 _115095 y x z)) = True.
Proof. exact (TRANS (@lem5131467 _115095 y x z) (@lem5131471 _115095 y x z)). Qed.
Lemma lem5131473 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : True = ((term567 _115095 x y z) = (term601 _115095 y x z)).
Proof. exact (SYM (@lem5131472 _115095 y x z)). Qed.
Lemma lem5131474 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term567 _115095 x y z) = (term601 _115095 y x z).
Proof. exact (EQ_MP (@lem5131473 _115095 y x z) (@lem0)). Qed.
Lemma lem5131475 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : term601 _115095 y x z.
Proof. exact (EQ_MP (@lem5131474 _115095 y x z) (@lem5131236 _115095 x y z)). Qed.
Lemma lem5131477 (b : Prop) (a : Prop) : (a \/ b) = (term574 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5131478 {_115095 : Type'} (x : _115095) (y : _115095) (z : _115095) : (term601 _115095 y x z) = (term604 _115095 x y z).
Proof. exact (@lem5131477 (term605 _115095 y x z) (y = z)). Qed.
Lemma lem5131480 (a : Prop) (b : Prop) : (term606 a b) = (term607 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5131481 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term608 _115095 y x z) = (term609 _115095 y x z).
Proof. exact (@lem5131480 (term597 _115095 x y) (term597 _115095 x z)). Qed.
Lemma lem5131483 (a : Prop) : (term25 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5131484 {_115095 : Type'} (x : _115095) (y : _115095) : (term610 _115095 x y) = (x = y).
Proof. exact (@lem5131483 (x = y)). Qed.
Lemma lem5131485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5131486 {_115095 : Type'} (x : _115095) (y : _115095) : (term611 _115095 x y) = (term612 _115095 x y).
Proof. exact (MK_COMB (@lem5131485) (@lem5131484 _115095 x y)). Qed.
Lemma lem5131488 (a : Prop) : (term25 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5131489 {_115095 : Type'} (x : _115095) (z : _115095) : (term610 _115095 x z) = (x = z).
Proof. exact (@lem5131488 (x = z)). Qed.
Lemma lem5131490 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term609 _115095 y x z) = (term613 _115095 y x z).
Proof. exact (MK_COMB (@lem5131486 _115095 x y) (@lem5131489 _115095 x z)). Qed.
Lemma lem5131491 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term608 _115095 y x z) = (term613 _115095 y x z).
Proof. exact (TRANS (@lem5131481 _115095 y x z) (@lem5131490 _115095 y x z)). Qed.
Lemma lem5131492 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5131493 {_115095 : Type'} (y : _115095) (x : _115095) (z : _115095) : (term614 _115095 y x z) = (term615 _115095 y x z).
Proof. exact (MK_COMB (@lem5131492) (@lem5131491 _115095 y x z)). Qed.
Lemma lem5131494 {_115095 : Type'} (y : _115095) (z : _115095) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem5131495 {_115095 : Type'} (x : _115095) (y : _115095) (z : _115095) : (term604 _115095 x y z) = (term616 _115095 x y z).
Proof. exact (MK_COMB (@lem5131493 _115095 y x z) (@lem5131494 _115095 y z)). Qed.
Lemma lem5131496 {_115095 : Type'} (x : _115095) (y : _115095) (z : _115095) : (term601 _115095 y x z) = (term616 _115095 x y z).
Proof. exact (TRANS (@lem5131478 _115095 x y z) (@lem5131495 _115095 x y z)). Qed.
Lemma lem5131498 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term638 _115095 _115098 x y' f.
Proof. exact (conj (@lem5131376 _115095 _115098 y' t s f x h1) (@lem5131385 _115095 _115098 y' f)). Qed.
Lemma lem5131500 {_115095 : Type'} (x : _115095) (y : _115095) (z : _115095) : term616 _115095 x y z.
Proof. exact (EQ_MP (@lem5131496 _115095 x y z) (@lem5131475 _115095 y x z)). Qed.
Lemma lem5131501 {_115095 : Type'} (x : _115095) (y : _115095) (z : _115095) : term616 _115095 x y z.
Proof. exact (@lem5131500 _115095 x y z). Qed.
Lemma lem5131502 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : term639 _115095 _115098 x y' f.
Proof. exact (@lem5131501 _115095 (@I ((_115098 -> _115095) -> _115095) y' f) (term590 _115095 _115098 x y' f) (@I ((_115098 -> _115095) -> _115095) y' f)). Qed.
Lemma lem5131505 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : (term590 _115095 _115098 x y' f) = (@I ((_115098 -> _115095) -> _115095) y' f).
Proof. exact (@lem5131502 _115095 _115098 x y' f (@lem5131498 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5131506 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term591 _115095 _115098 x y' f.
Proof. exact (fun h0 : term592 _115095 _115098 x y' f => @lem5131505 _115095 _115098 y' t s f x h1). Qed.
Lemma lem5131508 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5131509 {_115095 _115098 : Type'} (x : _115095 -> _115098) (y' : type802 _115095 _115098) (f : _115098 -> _115095) : (term591 _115095 _115098 x y' f) = ((term590 _115095 _115098 x y' f) = (@I ((_115098 -> _115095) -> _115095) y' f)).
Proof. exact (@lem5131508 ((term590 _115095 _115098 x y' f) = (@I ((_115098 -> _115095) -> _115095) y' f))). Qed.
Lemma lem5131510 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : (term590 _115095 _115098 x y' f) = (@I ((_115098 -> _115095) -> _115095) y' f).
Proof. exact (EQ_MP (@lem5131509 _115095 _115098 x y' f) (@lem5131506 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5131512 (a : Prop) (b : Prop) : (term621 a b) = (term622 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5131513 {_115095 _115098 : Type'} (s : _115098 -> Prop) (_66982 : _115098) (y' : type802 _115095 _115098) (_66981 : _115098 -> _115095) : (term479 _115095 _115098 s _66982 y' _66981) = (term640 _115095 _115098 s _66982 y' _66981).
Proof. exact (@lem5131512 (term468 _115098 _66982 s) ((@I (_115098 -> _115095) _66981 _66982) = (@I ((_115098 -> _115095) -> _115095) y' _66981))). Qed.
Lemma lem5131515 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5131516 {_115095 _115098 : Type'} (s : _115098 -> Prop) (_66982 : _115098) (y' : type802 _115095 _115098) (_66981 : _115098 -> _115095) : (term640 _115095 _115098 s _66982 y' _66981) = (term641 _115095 _115098 s _66982 y' _66981).
Proof. exact (@lem5131515 (term642 _115095 _115098 s _66982 y' _66981)). Qed.
Lemma lem5131517 {_115095 _115098 : Type'} (s : _115098 -> Prop) (_66982 : _115098) (y' : type802 _115095 _115098) (_66981 : _115098 -> _115095) : (term479 _115095 _115098 s _66982 y' _66981) = (term641 _115095 _115098 s _66982 y' _66981).
Proof. exact (TRANS (@lem5131513 _115095 _115098 s _66982 y' _66981) (@lem5131516 _115095 _115098 s _66982 y' _66981)). Qed.
Lemma lem5131519 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term643 _115095 _115098 s x y' f.
Proof. exact (conj (@lem5131310 _115095 _115098 y' t s f x h1) (@lem5131510 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5131521 {_115095 _115098 : Type'} (_66982 : _115098) (_66981 : _115098 -> _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term641 _115095 _115098 s _66982 y' _66981.
Proof. exact (EQ_MP (@lem5131517 _115095 _115098 s _66982 y' _66981) (@lem5130695 _115095 _115098 _66982 _66981 y' t s f x h1)). Qed.
Lemma lem5131522 {_115095 _115098 : Type'} (_66982 : _115098) (_66981 : _115098 -> _115095) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term641 _115095 _115098 s _66982 y' _66981.
Proof. exact (@lem5131521 _115095 _115098 _66982 _66981 y' t s f x h1). Qed.
Lemma lem5131523 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term644 _115095 _115098 s x y' f.
Proof. exact (@lem5131522 _115095 _115098 (term628 _115095 _115098 x y' f) f y' t s f x h1). Qed.
Lemma lem5131526 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : False.
Proof. exact (@lem5131523 _115095 _115098 y' t s f x h1 (@lem5131519 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5131527 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : term629.
Proof. exact (fun h0 : ~ False => @lem5131526 _115095 _115098 y' t s f x h1). Qed.
Lemma lem5131529 (p : Prop) : (term570 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5131530 : term629 = False.
Proof. exact (@lem5131529 False). Qed.
Lemma lem5131531 {_115095 _115098 : Type'} (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term497 _115095 _115098 y' t s f x) : False.
Proof. exact (EQ_MP (@lem5131530) (@lem5131527 _115095 _115098 y' t s f x h1)). Qed.
Lemma lem5131532 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (x : _115095 -> _115098) (h1 : term442 _115095 _115098 g y y' t s f x) : False.
Proof. exact (or_elim (@lem5130493 _115095 _115098 g y y' t s f x h1) (fun h0 : term519 _115095 _115098 g y t s y' => @lem5131113 _115095 _115098 g y t s y' h0) (fun h0 : term497 _115095 _115098 y' t s f x => @lem5131531 _115095 _115098 y' t s f x h0)). Qed.
Lemma lem5131533 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (f : _115098 -> _115095) (h1 : term445 _115095 _115098 g y y' t s f) : False.
Proof. exact (ex_elim (@lem5130189 _115095 _115098 g y y' t s f h1) (fun x : _115095 -> _115098 => fun h0 : term444 _115095 _115098 g y y' t s f x => @lem5131532 _115095 _115098 g y y' t s f x h0)). Qed.
Lemma lem5131534 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (y' : type802 _115095 _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (h1 : term447 _115095 _115098 g y y' t s) : False.
Proof. exact (ex_elim (@lem5130188 _115095 _115098 g y y' t s h1) (fun f : _115098 -> _115095 => fun h0 : term446 _115095 _115098 g y y' t s f => @lem5131533 _115095 _115098 g y y' t s f h0)). Qed.
Lemma lem5131535 {_115095 _115098 : Type'} (g : _115098 -> _115095) (y : _115095 -> _115098) (t : _115095 -> Prop) (s : _115098 -> Prop) (h1 : term449 _115095 _115098 g y t s) : False.
Proof. exact (ex_elim (@lem5130187 _115095 _115098 g y t s h1) (fun y' : type802 _115095 _115098 => fun h0 : term448 _115095 _115098 g y t s y' => @lem5131534 _115095 _115098 g y y' t s h0)). Qed.
Lemma lem5131536 {_115095 _115098 : Type'} (g : _115098 -> _115095) (t : _115095 -> Prop) (s : _115098 -> Prop) (h1 : term451 _115095 _115098 g t s) : False.
Proof. exact (ex_elim (@lem5130186 _115095 _115098 g t s h1) (fun y : _115095 -> _115098 => fun h0 : term450 _115095 _115098 g t s y => @lem5131535 _115095 _115098 g y t s h0)). Qed.
Lemma lem5131537 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (h1 : term42 _115095 _115098 t s) : False.
Proof. exact (ex_elim (@lem5130185 _115095 _115098 t s h1) (fun g : _115098 -> _115095 => fun h0 : term452 _115095 _115098 t s g => @lem5131536 _115095 _115098 g t s h0)). Qed.
Lemma lem5131538 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (h1 : term42 _115095 _115098 t s) : (term42 _115095 _115098 t s) = False.
Proof. exact (prop_ext (fun h2 : term42 _115095 _115098 t s => @lem5131537 _115095 _115098 t s h1) (fun h2 : False => @lem5129161 _115095 _115098 t s h1)). Qed.
Lemma lem5131539 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) (h1 : term42 _115095 _115098 t s) : False.
Proof. exact (EQ_MP (@lem5131538 _115095 _115098 t s h1) (@lem5129161 _115095 _115098 t s h1)). Qed.
Lemma lem5131540 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : term41 _115095 _115098 t s.
Proof. exact (fun h0 : term42 _115095 _115098 t s => @lem5131539 _115095 _115098 t s h0). Qed.
Lemma lem5131541 {_115095 _115098 : Type'} (t : _115095 -> Prop) (s : _115098 -> Prop) : (term3 _115095 _115098 t s) = (term9 _115095 _115098 t s).
Proof. exact (EQ_MP (@lem5129160 _115095 _115098 t s) (@lem5131540 _115095 _115098 t s)). Qed.
Lemma lem5131546 {_115095 _115098 : Type'} (s : _115098 -> Prop) : term13 _115095 _115098 s.
Proof. exact (fun t : _115095 -> Prop => @lem5131541 _115095 _115098 t s). Qed.
Lemma lem5131551 {_115095 _115098 : Type'} : term17 _115095 _115098.
Proof. exact (fun s : _115098 -> Prop => @lem5131546 _115095 _115098 s). Qed.
Lemma lem5131552 {_115095 _115098 : Type'} : term19 _115095 _115098.
Proof. exact (EQ_MP (@lem5129156 _115095 _115098) (@lem5131551 _115095 _115098)). Qed.
Lemma lem5131554 {_115095 _115098 : Type'} : term19 _115095 _115098.
Proof. exact (@lem5128912 _115095 _115098 (@lem5131552 _115095 _115098)). Qed.
Lemma lem5131555 {_115095 _115098 : Type'} (h1 : term20 _115095 _115098) : False.
Proof. exact (@lem5131554 _115095 _115098 (@lem5128896 _115095 _115098 h1)). Qed.
Lemma lem5131556 {_115095 _115098 : Type'} (h1 : term20 _115095 _115098) : (term20 _115095 _115098) = False.
Proof. exact (prop_ext (fun h2 : term20 _115095 _115098 => @lem5131555 _115095 _115098 h1) (fun h2 : False => @lem5128896 _115095 _115098 h1)). Qed.
Lemma lem5131557 {_115095 _115098 : Type'} (h1 : term20 _115095 _115098) : False.
Proof. exact (EQ_MP (@lem5131556 _115095 _115098 h1) (@lem5128896 _115095 _115098 h1)). Qed.
Lemma lem5131558 {_115095 _115098 : Type'} : term19 _115095 _115098.
Proof. exact (fun h0 : term20 _115095 _115098 => @lem5131557 _115095 _115098 h0). Qed.
Lemma lem5131559 {_115095 _115098 : Type'} : term17 _115095 _115098.
Proof. exact (EQ_MP (@lem5128895 _115095 _115098) (@lem5131558 _115095 _115098)). Qed.
Lemma lem5131560 {_115095 _115098 : Type'} : term16 _115095 _115098.
Proof. exact (EQ_MP (@lem5128891 _115095 _115098) (@lem5131559 _115095 _115098)). Qed.
