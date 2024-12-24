Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318030_term_abbrevs.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_EQ_TRANS_spec.
Require Import NADD_MUL_WELLDEF_spec.
Require Import thm1317744_spec.
Require Import thm32_spec.
Require Import thm9127_spec.
Lemma lem1317913 : hreal_mul = term0.
Proof. exact (@hreal_mul_def). Qed.
Lemma lem1317914 (x : hreal) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1317915 (x : hreal) : (hreal_mul x) = (term1 x).
Proof. exact (MK_COMB (@lem1317913) (@lem1317914 x)). Qed.
Lemma lem1317916 (x : hreal) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1317917 (x : hreal) : (term3 x) = (term3 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1317918 (x : hreal) : ((hreal_mul x) = (term1 x)) = ((hreal_mul x) = (term2 x)).
Proof. exact (MK_COMB (@lem1317917 x) (@lem1317916 x)). Qed.
Lemma lem1317919 (x : hreal) : (hreal_mul x) = (term2 x).
Proof. exact (EQ_MP (@lem1317918 x) (@lem1317915 x)). Qed.
Lemma lem1317920 (y : hreal) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1317921 (x : hreal) (y : hreal) : (hreal_mul x y) = (term4 x y).
Proof. exact (MK_COMB (@lem1317919 x) (@lem1317920 y)). Qed.
Lemma lem1317922 (x : hreal) (y : hreal) : (term4 x y) = (term5 x y).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1317923 (x : hreal) (y : hreal) : (term6 x y) = (term6 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1317924 (x : hreal) (y : hreal) : ((hreal_mul x y) = (term4 x y)) = ((hreal_mul x y) = (term5 x y)).
Proof. exact (MK_COMB (@lem1317923 x y) (@lem1317922 x y)). Qed.
Lemma lem1317925 (x : hreal) (y : hreal) : (hreal_mul x y) = (term5 x y).
Proof. exact (EQ_MP (@lem1317924 x y) (@lem1317921 x y)). Qed.
Lemma lem1317926 (x : nadd) : (term7 x) = ((term8 x) = (nadd_eq x)).
Proof. exact (@lem1317744 (nadd_eq x)). Qed.
Lemma lem1317927 (x : nadd) : (nadd_eq x) = (nadd_eq x).
Proof. exact (eq_refl (nadd_eq x)). Qed.
Lemma lem1317928 (x : nadd) : term7 x.
Proof. exact (ex_intro (term9 x) x (@lem1317927 x)). Qed.
Lemma lem1317929 (x : nadd) : (term8 x) = (nadd_eq x).
Proof. exact (EQ_MP (@lem1317926 x) (@lem1317928 x)). Qed.
Lemma lem1317930 (x : nadd) (y : nadd) : (term10 x y) = (term11 x y).
Proof. exact (@lem1317925 (term12 x) (term12 y)). Qed.
Lemma lem1317931 (x : nadd) : (term8 x) = (nadd_eq x).
Proof. exact (@lem1317929 x). Qed.
Lemma lem1317932 (y : nadd) : (term8 y) = (nadd_eq y).
Proof. exact (@lem1317929 y). Qed.
Lemma lem1317933 (x : nadd) (y : nadd) : (term13 x y) = (term13 x y).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1317934 (y : nadd) (x : nadd) : (term14 y x) = (term15 y x).
Proof. exact (MK_COMB (@lem1317933 x y) (@lem1317931 x)). Qed.
Lemma lem1317935 (y : nadd) (x : nadd) : (term15 y x) = (term16 y x).
Proof. exact (eq_refl (term15 y x)). Qed.
Lemma lem1317936 (y : nadd) (x : nadd) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem1317937 (y : nadd) (x : nadd) : ((term14 y x) = (term15 y x)) = ((term14 y x) = (term16 y x)).
Proof. exact (MK_COMB (@lem1317936 y x) (@lem1317935 y x)). Qed.
Lemma lem1317938 (y : nadd) (x : nadd) : (term14 y x) = (term18 y x).
Proof. exact (eq_refl (term14 y x)). Qed.
Lemma lem1317939 : (@eq ((nadd -> Prop) -> Prop)) = (@eq ((nadd -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((nadd -> Prop) -> Prop))). Qed.
Lemma lem1317940 (y : nadd) (x : nadd) : (term17 y x) = (term19 y x).
Proof. exact (MK_COMB (@lem1317939) (@lem1317938 y x)). Qed.
Lemma lem1317941 (y : nadd) (x : nadd) : (term16 y x) = (term16 y x).
Proof. exact (eq_refl (term16 y x)). Qed.
Lemma lem1317942 (y : nadd) (x : nadd) : ((term14 y x) = (term16 y x)) = ((term18 y x) = (term16 y x)).
Proof. exact (MK_COMB (@lem1317940 y x) (@lem1317941 y x)). Qed.
Lemma lem1317943 (y : nadd) (x : nadd) : ((term14 y x) = (term15 y x)) = ((term18 y x) = (term16 y x)).
Proof. exact (TRANS (@lem1317937 y x) (@lem1317942 y x)). Qed.
Lemma lem1317944 (y : nadd) (x : nadd) : (term18 y x) = (term16 y x).
Proof. exact (EQ_MP (@lem1317943 y x) (@lem1317934 y x)). Qed.
Lemma lem1317945 (x : nadd) (y : nadd) : (term20 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem1317944 y x) (@lem1317932 y)). Qed.
Lemma lem1317946 (x : nadd) (y : nadd) : (term21 x y) = ((term10 x y) = (term22 x y)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1317947 (x : nadd) (y : nadd) : (term23 x y) = (term23 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1317948 (x : nadd) (y : nadd) : ((term20 x y) = (term21 x y)) = ((term20 x y) = ((term10 x y) = (term22 x y))).
Proof. exact (MK_COMB (@lem1317947 x y) (@lem1317946 x y)). Qed.
Lemma lem1317949 (x : nadd) (y : nadd) : (term20 x y) = ((term10 x y) = (term11 x y)).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1317950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1317951 (x : nadd) (y : nadd) : (term23 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem1317950) (@lem1317949 x y)). Qed.
Lemma lem1317952 (x : nadd) (y : nadd) : ((term10 x y) = (term22 x y)) = ((term10 x y) = (term22 x y)).
Proof. exact (eq_refl ((term10 x y) = (term22 x y))). Qed.
Lemma lem1317953 (x : nadd) (y : nadd) : ((term20 x y) = ((term10 x y) = (term22 x y))) = (((term10 x y) = (term11 x y)) = ((term10 x y) = (term22 x y))).
Proof. exact (MK_COMB (@lem1317951 x y) (@lem1317952 x y)). Qed.
Lemma lem1317954 (x : nadd) (y : nadd) : ((term20 x y) = (term21 x y)) = (((term10 x y) = (term11 x y)) = ((term10 x y) = (term22 x y))).
Proof. exact (TRANS (@lem1317948 x y) (@lem1317953 x y)). Qed.
Lemma lem1317955 (x : nadd) (y : nadd) : ((term10 x y) = (term11 x y)) = ((term10 x y) = (term22 x y)).
Proof. exact (EQ_MP (@lem1317954 x y) (@lem1317945 x y)). Qed.
Lemma lem1317956 (x : nadd) (y : nadd) : (term10 x y) = (term22 x y).
Proof. exact (EQ_MP (@lem1317955 x y) (@lem1317930 x y)). Qed.
Lemma lem1317957 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term25 u x x' y y'.
Proof. exact (h1). Qed.
Lemma lem1317958 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term26 x x' y y'.
Proof. exact (proj2 (@lem1317957 u x x' y y' h1)). Qed.
Lemma lem1317959 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term27 x' y' u.
Proof. exact (proj1 (@lem1317957 u x x' y y' h1)). Qed.
Lemma lem1317960 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : nadd_eq y y'.
Proof. exact (proj2 (@lem1317958 u x x' y y' h1)). Qed.
Lemma lem1317961 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : nadd_eq x x'.
Proof. exact (proj1 (@lem1317958 u x x' y y' h1)). Qed.
Lemma lem1317962 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term26 x x' y y'.
Proof. exact (conj (@lem1317961 u x x' y y' h1) (@lem1317960 u x x' y y' h1)). Qed.
Lemma lem1317963 (x : nadd) : term28 x.
Proof. exact (@lem1279298 x). Qed.
Lemma lem1317964 (x : nadd) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1317965 (x : nadd) : term29 x.
Proof. exact (EQ_MP (@lem1317964 x) (@lem1317963 x)). Qed.
Lemma lem1317966 (x : nadd) (x' : nadd) : term30 x x'.
Proof. exact (@lem1317965 x x'). Qed.
Lemma lem1317967 (x : nadd) (x' : nadd) : (term30 x x') = (term31 x x').
Proof. exact (eq_refl (term30 x x')). Qed.
Lemma lem1317968 (x : nadd) (x' : nadd) : term31 x x'.
Proof. exact (EQ_MP (@lem1317967 x x') (@lem1317966 x x')). Qed.
Lemma lem1317969 (x : nadd) (x' : nadd) (y : nadd) : term32 x x' y.
Proof. exact (@lem1317968 x x' y). Qed.
Lemma lem1317970 (x : nadd) (y : nadd) (x' : nadd) : (term32 x x' y) = (term33 x y x').
Proof. exact (eq_refl (term32 x x' y)). Qed.
Lemma lem1317971 (x : nadd) (y : nadd) (x' : nadd) : term33 x y x'.
Proof. exact (EQ_MP (@lem1317970 x y x') (@lem1317969 x x' y)). Qed.
Lemma lem1317972 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term34 x y x' y'.
Proof. exact (@lem1317971 x y x' y'). Qed.
Lemma lem1317973 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term34 x y x' y') = (term35 x y x' y').
Proof. exact (eq_refl (term34 x y x' y')). Qed.
Lemma lem1317976 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term35 x y x' y'.
Proof. exact (EQ_MP (@lem1317973 x y x' y') (@lem1317972 x y x' y')). Qed.
Lemma lem1317977 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term36 x y x' y'.
Proof. exact (@lem1317976 x y x' y' (@lem1317962 u x x' y y' h1)). Qed.
Lemma lem1317978 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term37 x y x' y' u.
Proof. exact (conj (@lem1317977 u x x' y y' h1) (@lem1317959 u x x' y y' h1)). Qed.
Lemma lem1317979 (x : nadd) : term38 x.
Proof. exact (@lem1268295 x). Qed.
Lemma lem1317980 (x : nadd) : (term38 x) = (term39 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1317981 (x : nadd) : term39 x.
Proof. exact (EQ_MP (@lem1317980 x) (@lem1317979 x)). Qed.
Lemma lem1317982 (x : nadd) (y : nadd) : term40 x y.
Proof. exact (@lem1317981 x y). Qed.
Lemma lem1317983 (y : nadd) (x : nadd) : (term40 x y) = (term41 y x).
Proof. exact (eq_refl (term40 x y)). Qed.
Lemma lem1317984 (y : nadd) (x : nadd) : term41 y x.
Proof. exact (EQ_MP (@lem1317983 y x) (@lem1317982 x y)). Qed.
Lemma lem1317985 (y : nadd) (x : nadd) (z : nadd) : term42 y x z.
Proof. exact (@lem1317984 y x z). Qed.
Lemma lem1317986 (y : nadd) (x : nadd) (z : nadd) : (term42 y x z) = (term43 y x z).
Proof. exact (eq_refl (term42 y x z)). Qed.
Lemma lem1317989 (y : nadd) (x : nadd) (z : nadd) : term43 y x z.
Proof. exact (EQ_MP (@lem1317986 y x z) (@lem1317985 y x z)). Qed.
Lemma lem1317990 (x' : nadd) (y' : nadd) (x : nadd) (y : nadd) (u : nadd) : term44 x' y' x y u.
Proof. exact (@lem1317989 (nadd_mul x' y') (nadd_mul x y) u). Qed.
Lemma lem1317991 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term27 x y u.
Proof. exact (@lem1317990 x' y' x y u (@lem1317978 u x x' y y' h1)). Qed.
Lemma lem1317992 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (h1 : term45 u x x' y) : term45 u x x' y.
Proof. exact (h1). Qed.
Lemma lem1317993 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (h1 : term45 u x x' y) : term27 x y u.
Proof. exact (ex_elim (@lem1317992 u x x' y h1) (fun y' : nadd => fun h0 : term46 u x x' y y' => @lem1317991 u x x' y y' h0)). Qed.
Lemma lem1317994 (u : nadd) (x : nadd) (y : nadd) (h1 : term47 u x y) : term47 u x y.
Proof. exact (h1). Qed.
Lemma lem1317995 (u : nadd) (x : nadd) (y : nadd) (h1 : term47 u x y) : term27 x y u.
Proof. exact (ex_elim (@lem1317994 u x y h1) (fun x' : nadd => fun h0 : term48 u x y x' => @lem1317993 u x x' y h0)). Qed.
Lemma lem1317996 (x : nadd) (y : nadd) (u : nadd) (h1 : term27 x y u) : term27 x y u.
Proof. exact (h1). Qed.
Lemma lem1317997 (x : nadd) : term49 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1317998 (x : nadd) : (term49 x) = (nadd_eq x x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1317999 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1317998 x) (@lem1317997 x)). Qed.
Lemma lem1318000 (y : nadd) : term49 y.
Proof. exact (@lem1267990 y). Qed.
Lemma lem1318001 (y : nadd) : (term49 y) = (nadd_eq y y).
Proof. exact (eq_refl (term49 y)). Qed.
Lemma lem1318002 (y : nadd) : nadd_eq y y.
Proof. exact (EQ_MP (@lem1318001 y) (@lem1318000 y)). Qed.
Lemma lem1318003 (x : nadd) (y : nadd) : term50 x y.
Proof. exact (conj (@lem1317999 x) (@lem1318002 y)). Qed.
Lemma lem1318004 (x : nadd) (y : nadd) (u : nadd) (h1 : term27 x y u) : term51 u x y.
Proof. exact (conj (@lem1317996 x y u h1) (@lem1318003 x y)). Qed.
Lemma lem1318005 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term25 u x x' y y'.
Proof. exact (h1). Qed.
Lemma lem1318006 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term45 u x x' y.
Proof. exact (ex_intro (term46 u x x' y) y' (@lem1318005 u x x' y y' h1)). Qed.
Lemma lem1318007 (u : nadd) (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term25 u x x' y y') : term47 u x y.
Proof. exact (ex_intro (term48 u x y) x' (@lem1318006 u x x' y y' h1)). Qed.
Lemma lem1318010 (x' : nadd) (y' : nadd) (u : nadd) (x : nadd) (y : nadd) : term52 x' y' u x y.
Proof. exact (fun h0 : term25 u x x' y y' => @lem1318007 u x x' y y' h0). Qed.
Lemma lem1318011 (u : nadd) (x : nadd) (y : nadd) : term53 u x y.
Proof. exact (@lem1318010 x y u x y). Qed.
Lemma lem1318012 (x : nadd) (y : nadd) (u : nadd) (h1 : term27 x y u) : term47 u x y.
Proof. exact (@lem1318011 u x y (@lem1318004 x y u h1)). Qed.
Lemma lem1318013 (u : nadd) (x : nadd) (y : nadd) : term54 u x y.
Proof. exact (fun h0 : term27 x y u => @lem1318012 x y u h0). Qed.
Lemma lem1318014 (x : nadd) (y : nadd) (u : nadd) : term55 x y u.
Proof. exact (fun h0 : term47 u x y => @lem1317995 u x y h0). Qed.
Lemma lem1318015 (u : nadd) (x : nadd) (y : nadd) : term56 u x y.
Proof. exact (conj (@lem1318014 x y u) (@lem1318013 u x y)). Qed.
Lemma lem1318016 (x : nadd) (y : nadd) (u : nadd) : (term56 u x y) = ((term47 u x y) = (term27 x y u)).
Proof. exact (@lem32 (term47 u x y) (term27 x y u)). Qed.
Lemma lem1318017 (x : nadd) (y : nadd) (u : nadd) : (term47 u x y) = (term27 x y u).
Proof. exact (EQ_MP (@lem1318016 x y u) (@lem1318015 u x y)). Qed.
Lemma lem1318018 (x : nadd) (y : nadd) : (term57 x y) = (term58 x y).
Proof. exact (fun_ext (fun u : nadd => @lem1318017 x y u)). Qed.
Lemma lem1318019 : mk_hreal = mk_hreal.
Proof. exact (eq_refl mk_hreal). Qed.
Lemma lem1318020 (x : nadd) (y : nadd) : (term22 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1318019) (@lem1318018 x y)). Qed.
Lemma lem1318021 (x : nadd) (y : nadd) : (term10 x y) = (term59 x y).
Proof. exact (TRANS (@lem1317956 x y) (@lem1318020 x y)). Qed.
Lemma lem1318022 (t : nadd -> Prop) : (term60 t) = t.
Proof. exact (@lem9127 nadd Prop t). Qed.
Lemma lem1318025 (x : nadd) (y : nadd) : (term58 x y) = (term61 x y).
Proof. exact (@lem1318022 (term61 x y)). Qed.
Lemma lem1318026 : mk_hreal = mk_hreal.
Proof. exact (eq_refl mk_hreal). Qed.
Lemma lem1318027 (x : nadd) (y : nadd) : (term59 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1318026) (@lem1318025 x y)). Qed.
Lemma lem1318028 (x : nadd) (y : nadd) : (term63 x y) = (term63 x y).
Proof. exact (eq_refl (term63 x y)). Qed.
Lemma lem1318029 (x : nadd) (y : nadd) : ((term10 x y) = (term59 x y)) = ((term10 x y) = (term62 x y)).
Proof. exact (MK_COMB (@lem1318028 x y) (@lem1318027 x y)). Qed.
Lemma lem1318030 (x : nadd) (y : nadd) : (term10 x y) = (term62 x y).
Proof. exact (EQ_MP (@lem1318029 x y) (@lem1318021 x y)). Qed.
