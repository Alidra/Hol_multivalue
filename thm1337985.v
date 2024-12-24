Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1337985_term_abbrevs.
Require Import TREAL_EQ_REFL_spec.
Require Import TREAL_LE_WELLDEF_spec.
Require Import thm1337493_spec.
Require Import thm23443_spec.
Require Import thm32_spec.
Lemma lem1337879 : real_le = term0.
Proof. exact (@real_le_def). Qed.
Lemma lem1337880 (x1 : real) : x1 = x1.
Proof. exact (eq_refl x1). Qed.
Lemma lem1337881 (x1 : real) : (real_le x1) = (term1 x1).
Proof. exact (MK_COMB (@lem1337879) (@lem1337880 x1)). Qed.
Lemma lem1337882 (x1 : real) : (term1 x1) = (term2 x1).
Proof. exact (eq_refl (term1 x1)). Qed.
Lemma lem1337883 (x1 : real) : (term3 x1) = (term3 x1).
Proof. exact (eq_refl (term3 x1)). Qed.
Lemma lem1337884 (x1 : real) : ((real_le x1) = (term1 x1)) = ((real_le x1) = (term2 x1)).
Proof. exact (MK_COMB (@lem1337883 x1) (@lem1337882 x1)). Qed.
Lemma lem1337885 (x1 : real) : (real_le x1) = (term2 x1).
Proof. exact (EQ_MP (@lem1337884 x1) (@lem1337881 x1)). Qed.
Lemma lem1337886 (y1 : real) : y1 = y1.
Proof. exact (eq_refl y1). Qed.
Lemma lem1337887 (x1 : real) (y1 : real) : (real_le x1 y1) = (term4 x1 y1).
Proof. exact (MK_COMB (@lem1337885 x1) (@lem1337886 y1)). Qed.
Lemma lem1337888 (x1 : real) (y1 : real) : (term4 x1 y1) = (term5 x1 y1).
Proof. exact (eq_refl (term4 x1 y1)). Qed.
Lemma lem1337889 (x1 : real) (y1 : real) : (term6 x1 y1) = (term6 x1 y1).
Proof. exact (eq_refl (term6 x1 y1)). Qed.
Lemma lem1337890 (x1 : real) (y1 : real) : ((real_le x1 y1) = (term4 x1 y1)) = ((real_le x1 y1) = (term5 x1 y1)).
Proof. exact (MK_COMB (@lem1337889 x1 y1) (@lem1337888 x1 y1)). Qed.
Lemma lem1337891 (x1 : real) (y1 : real) : (real_le x1 y1) = (term5 x1 y1).
Proof. exact (EQ_MP (@lem1337890 x1 y1) (@lem1337887 x1 y1)). Qed.
Lemma lem1337892 (x : prod hreal hreal) : (term7 x) = ((term8 x) = (treal_eq x)).
Proof. exact (@lem1337493 (treal_eq x)). Qed.
Lemma lem1337893 (x : prod hreal hreal) : (treal_eq x) = (treal_eq x).
Proof. exact (eq_refl (treal_eq x)). Qed.
Lemma lem1337894 (x : prod hreal hreal) : term7 x.
Proof. exact (ex_intro (term9 x) x (@lem1337893 x)). Qed.
Lemma lem1337895 (x : prod hreal hreal) : (term8 x) = (treal_eq x).
Proof. exact (EQ_MP (@lem1337892 x) (@lem1337894 x)). Qed.
Lemma lem1337896 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term10 x1 y1) = (term11 x1 y1).
Proof. exact (@lem1337891 (term12 x1) (term12 y1)). Qed.
Lemma lem1337897 (x1 : prod hreal hreal) : (term8 x1) = (treal_eq x1).
Proof. exact (@lem1337895 x1). Qed.
Lemma lem1337898 (y1 : prod hreal hreal) : (term8 y1) = (treal_eq y1).
Proof. exact (@lem1337895 y1). Qed.
Lemma lem1337899 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term13 x1 y1) = (term13 x1 y1).
Proof. exact (eq_refl (term13 x1 y1)). Qed.
Lemma lem1337900 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term14 y1 x1) = (term15 y1 x1).
Proof. exact (MK_COMB (@lem1337899 x1 y1) (@lem1337897 x1)). Qed.
Lemma lem1337901 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term15 y1 x1) = (term16 y1 x1).
Proof. exact (eq_refl (term15 y1 x1)). Qed.
Lemma lem1337902 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term17 y1 x1) = (term17 y1 x1).
Proof. exact (eq_refl (term17 y1 x1)). Qed.
Lemma lem1337903 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : ((term14 y1 x1) = (term15 y1 x1)) = ((term14 y1 x1) = (term16 y1 x1)).
Proof. exact (MK_COMB (@lem1337902 y1 x1) (@lem1337901 y1 x1)). Qed.
Lemma lem1337904 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term14 y1 x1) = (term18 y1 x1).
Proof. exact (eq_refl (term14 y1 x1)). Qed.
Lemma lem1337905 : (@eq (((prod hreal hreal) -> Prop) -> Prop)) = (@eq (((prod hreal hreal) -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq (((prod hreal hreal) -> Prop) -> Prop))). Qed.
Lemma lem1337906 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term17 y1 x1) = (term19 y1 x1).
Proof. exact (MK_COMB (@lem1337905) (@lem1337904 y1 x1)). Qed.
Lemma lem1337907 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term16 y1 x1) = (term16 y1 x1).
Proof. exact (eq_refl (term16 y1 x1)). Qed.
Lemma lem1337908 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : ((term14 y1 x1) = (term16 y1 x1)) = ((term18 y1 x1) = (term16 y1 x1)).
Proof. exact (MK_COMB (@lem1337906 y1 x1) (@lem1337907 y1 x1)). Qed.
Lemma lem1337909 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : ((term14 y1 x1) = (term15 y1 x1)) = ((term18 y1 x1) = (term16 y1 x1)).
Proof. exact (TRANS (@lem1337903 y1 x1) (@lem1337908 y1 x1)). Qed.
Lemma lem1337910 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term18 y1 x1) = (term16 y1 x1).
Proof. exact (EQ_MP (@lem1337909 y1 x1) (@lem1337900 y1 x1)). Qed.
Lemma lem1337911 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term20 x1 y1) = (term21 x1 y1).
Proof. exact (MK_COMB (@lem1337910 y1 x1) (@lem1337898 y1)). Qed.
Lemma lem1337912 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term21 x1 y1) = ((term10 x1 y1) = (term22 x1 y1)).
Proof. exact (eq_refl (term21 x1 y1)). Qed.
Lemma lem1337913 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term23 x1 y1) = (term23 x1 y1).
Proof. exact (eq_refl (term23 x1 y1)). Qed.
Lemma lem1337914 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term20 x1 y1) = (term21 x1 y1)) = ((term20 x1 y1) = ((term10 x1 y1) = (term22 x1 y1))).
Proof. exact (MK_COMB (@lem1337913 x1 y1) (@lem1337912 x1 y1)). Qed.
Lemma lem1337915 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term20 x1 y1) = ((term10 x1 y1) = (term11 x1 y1)).
Proof. exact (eq_refl (term20 x1 y1)). Qed.
Lemma lem1337916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1337917 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term23 x1 y1) = (term24 x1 y1).
Proof. exact (MK_COMB (@lem1337916) (@lem1337915 x1 y1)). Qed.
Lemma lem1337918 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term10 x1 y1) = (term22 x1 y1)) = ((term10 x1 y1) = (term22 x1 y1)).
Proof. exact (eq_refl ((term10 x1 y1) = (term22 x1 y1))). Qed.
Lemma lem1337919 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term20 x1 y1) = ((term10 x1 y1) = (term22 x1 y1))) = (((term10 x1 y1) = (term11 x1 y1)) = ((term10 x1 y1) = (term22 x1 y1))).
Proof. exact (MK_COMB (@lem1337917 x1 y1) (@lem1337918 x1 y1)). Qed.
Lemma lem1337920 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term20 x1 y1) = (term21 x1 y1)) = (((term10 x1 y1) = (term11 x1 y1)) = ((term10 x1 y1) = (term22 x1 y1))).
Proof. exact (TRANS (@lem1337914 x1 y1) (@lem1337919 x1 y1)). Qed.
Lemma lem1337921 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term10 x1 y1) = (term11 x1 y1)) = ((term10 x1 y1) = (term22 x1 y1)).
Proof. exact (EQ_MP (@lem1337920 x1 y1) (@lem1337911 x1 y1)). Qed.
Lemma lem1337922 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term10 x1 y1) = (term22 x1 y1).
Proof. exact (EQ_MP (@lem1337921 x1 y1) (@lem1337896 x1 y1)). Qed.
Lemma lem1337923 (u : Prop) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term25 u x1 x1' y1 y1'.
Proof. exact (h1). Qed.
Lemma lem1337924 (u : Prop) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term26 x1 x1' y1 y1'.
Proof. exact (proj2 (@lem1337923 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337925 (u : Prop) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : (treal_le x1' y1') = u.
Proof. exact (proj1 (@lem1337923 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337926 (u : Prop) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : treal_eq y1 y1'.
Proof. exact (proj2 (@lem1337924 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337927 (u : Prop) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : treal_eq x1 x1'.
Proof. exact (proj1 (@lem1337924 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337928 (u : Prop) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term26 x1 x1' y1 y1'.
Proof. exact (conj (@lem1337927 u x1 x1' y1 y1' h1) (@lem1337926 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337929 (x1 : prod hreal hreal) : term27 x1.
Proof. exact (@lem1334747 x1). Qed.
Lemma lem1337930 (x1 : prod hreal hreal) : (term27 x1) = (term28 x1).
Proof. exact (eq_refl (term27 x1)). Qed.
Lemma lem1337931 (x1 : prod hreal hreal) : term28 x1.
Proof. exact (EQ_MP (@lem1337930 x1) (@lem1337929 x1)). Qed.
Lemma lem1337932 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term29 x1 x2.
Proof. exact (@lem1337931 x1 x2). Qed.
Lemma lem1337933 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (term29 x1 x2) = (term30 x1 x2).
Proof. exact (eq_refl (term29 x1 x2)). Qed.
Lemma lem1337934 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term30 x1 x2.
Proof. exact (EQ_MP (@lem1337933 x1 x2) (@lem1337932 x1 x2)). Qed.
Lemma lem1337935 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) : term31 x1 x2 y1.
Proof. exact (@lem1337934 x1 x2 y1). Qed.
Lemma lem1337936 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) : (term31 x1 x2 y1) = (term32 x1 y1 x2).
Proof. exact (eq_refl (term31 x1 x2 y1)). Qed.
Lemma lem1337937 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) : term32 x1 y1 x2.
Proof. exact (EQ_MP (@lem1337936 x1 y1 x2) (@lem1337935 x1 x2 y1)). Qed.
Lemma lem1337938 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term33 x1 y1 x2 y2.
Proof. exact (@lem1337937 x1 y1 x2 y2). Qed.
Lemma lem1337939 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : (term33 x1 y1 x2 y2) = (term34 x1 y1 x2 y2).
Proof. exact (eq_refl (term33 x1 y1 x2 y2)). Qed.
Lemma lem1337942 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term34 x1 y1 x2 y2.
Proof. exact (EQ_MP (@lem1337939 x1 y1 x2 y2) (@lem1337938 x1 y1 x2 y2)). Qed.
Lemma lem1337943 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x1' : prod hreal hreal) (y1' : prod hreal hreal) : term34 x1 y1 x1' y1'.
Proof. exact (@lem1337942 x1 y1 x1' y1'). Qed.
Lemma lem1337944 (u : Prop) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : (treal_le x1 y1) = (treal_le x1' y1').
Proof. exact (@lem1337943 x1 y1 x1' y1' (@lem1337928 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337945 (u : Prop) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : (treal_le x1 y1) = u.
Proof. exact (TRANS (@lem1337944 u x1 x1' y1 y1' h1) (@lem1337925 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337946 (u : Prop) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (h1 : term35 u x1 x1' y1) : term35 u x1 x1' y1.
Proof. exact (h1). Qed.
Lemma lem1337947 (u : Prop) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (h1 : term35 u x1 x1' y1) : (treal_le x1 y1) = u.
Proof. exact (ex_elim (@lem1337946 u x1 x1' y1 h1) (fun y1' : prod hreal hreal => fun h0 : term36 u x1 x1' y1 y1' => @lem1337945 u x1 x1' y1 y1' h0)). Qed.
Lemma lem1337948 (u : Prop) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : term37 u x1 y1) : term37 u x1 y1.
Proof. exact (h1). Qed.
Lemma lem1337949 (u : Prop) (x1 : prod hreal hreal) (y1 : prod hreal hreal) (h1 : term37 u x1 y1) : (treal_le x1 y1) = u.
Proof. exact (ex_elim (@lem1337948 u x1 y1 h1) (fun x1' : prod hreal hreal => fun h0 : term38 u x1 y1 x1' => @lem1337947 u x1 x1' y1 h0)). Qed.
Lemma lem1337950 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : Prop) (h1 : (treal_le x1 y1) = u) : (treal_le x1 y1) = u.
Proof. exact (h1). Qed.
Lemma lem1337951 (x1 : prod hreal hreal) : term39 x1.
Proof. exact (@lem1326193 x1). Qed.
Lemma lem1337952 (x1 : prod hreal hreal) : (term39 x1) = (treal_eq x1 x1).
Proof. exact (eq_refl (term39 x1)). Qed.
Lemma lem1337953 (x1 : prod hreal hreal) : treal_eq x1 x1.
Proof. exact (EQ_MP (@lem1337952 x1) (@lem1337951 x1)). Qed.
Lemma lem1337954 (y1 : prod hreal hreal) : term39 y1.
Proof. exact (@lem1326193 y1). Qed.
Lemma lem1337955 (y1 : prod hreal hreal) : (term39 y1) = (treal_eq y1 y1).
Proof. exact (eq_refl (term39 y1)). Qed.
Lemma lem1337956 (y1 : prod hreal hreal) : treal_eq y1 y1.
Proof. exact (EQ_MP (@lem1337955 y1) (@lem1337954 y1)). Qed.
Lemma lem1337957 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term40 x1 y1.
Proof. exact (conj (@lem1337953 x1) (@lem1337956 y1)). Qed.
Lemma lem1337958 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : Prop) (h1 : (treal_le x1 y1) = u) : term41 u x1 y1.
Proof. exact (conj (@lem1337950 x1 y1 u h1) (@lem1337957 x1 y1)). Qed.
Lemma lem1337959 (u : Prop) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term25 u x1 x1' y1 y1'.
Proof. exact (h1). Qed.
Lemma lem1337960 (u : Prop) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term35 u x1 x1' y1.
Proof. exact (ex_intro (term36 u x1 x1' y1) y1' (@lem1337959 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337961 (u : Prop) (x1 : prod hreal hreal) (x1' : prod hreal hreal) (y1 : prod hreal hreal) (y1' : prod hreal hreal) (h1 : term25 u x1 x1' y1 y1') : term37 u x1 y1.
Proof. exact (ex_intro (term38 u x1 y1) x1' (@lem1337960 u x1 x1' y1 y1' h1)). Qed.
Lemma lem1337964 (x1' : prod hreal hreal) (y1' : prod hreal hreal) (u : Prop) (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term42 x1' y1' u x1 y1.
Proof. exact (fun h0 : term25 u x1 x1' y1 y1' => @lem1337961 u x1 x1' y1 y1' h0). Qed.
Lemma lem1337965 (u : Prop) (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term43 u x1 y1.
Proof. exact (@lem1337964 x1 y1 u x1 y1). Qed.
Lemma lem1337966 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : Prop) (h1 : (treal_le x1 y1) = u) : term37 u x1 y1.
Proof. exact (@lem1337965 u x1 y1 (@lem1337958 x1 y1 u h1)). Qed.
Lemma lem1337967 (u : Prop) (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term44 u x1 y1.
Proof. exact (fun h0 : (treal_le x1 y1) = u => @lem1337966 x1 y1 u h0). Qed.
Lemma lem1337968 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : Prop) : term45 x1 y1 u.
Proof. exact (fun h0 : term37 u x1 y1 => @lem1337949 u x1 y1 h0). Qed.
Lemma lem1337969 (u : Prop) (x1 : prod hreal hreal) (y1 : prod hreal hreal) : term46 u x1 y1.
Proof. exact (conj (@lem1337968 x1 y1 u) (@lem1337967 u x1 y1)). Qed.
Lemma lem1337970 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : Prop) : (term46 u x1 y1) = ((term37 u x1 y1) = ((treal_le x1 y1) = u)).
Proof. exact (@lem32 (term37 u x1 y1) ((treal_le x1 y1) = u)). Qed.
Lemma lem1337971 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (u : Prop) : (term37 u x1 y1) = ((treal_le x1 y1) = u).
Proof. exact (EQ_MP (@lem1337970 x1 y1 u) (@lem1337969 u x1 y1)). Qed.
Lemma lem1337972 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term47 x1 y1) = (term48 x1 y1).
Proof. exact (fun_ext (fun u : Prop => @lem1337971 x1 y1 u)). Qed.
Lemma lem1337973 : (@ε Prop) = (@ε Prop).
Proof. exact (eq_refl (@ε Prop)). Qed.
Lemma lem1337974 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term22 x1 y1) = (term49 x1 y1).
Proof. exact (MK_COMB (@lem1337973) (@lem1337972 x1 y1)). Qed.
Lemma lem1337975 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term10 x1 y1) = (term49 x1 y1).
Proof. exact (TRANS (@lem1337922 x1 y1) (@lem1337974 x1 y1)). Qed.
Lemma lem1337976 {A : Type'} (x : A) : term50 A x.
Proof. exact (@lem23443 A x). Qed.
Lemma lem1337977 {A : Type'} (x : A) : (term50 A x) = ((term51 A x) = x).
Proof. exact (eq_refl (term50 A x)). Qed.
Lemma lem1337980 {A : Type'} (x : A) : (term51 A x) = x.
Proof. exact (EQ_MP (@lem1337977 A x) (@lem1337976 A x)). Qed.
Lemma lem1337981 (x : Prop) : (term52 x) = x.
Proof. exact (@lem1337980 Prop x). Qed.
Lemma lem1337982 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term49 x1 y1) = (treal_le x1 y1).
Proof. exact (@lem1337981 (treal_le x1 y1)). Qed.
Lemma lem1337983 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term53 x1 y1) = (term53 x1 y1).
Proof. exact (eq_refl (term53 x1 y1)). Qed.
Lemma lem1337984 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : ((term10 x1 y1) = (term49 x1 y1)) = ((term10 x1 y1) = (treal_le x1 y1)).
Proof. exact (MK_COMB (@lem1337983 x1 y1) (@lem1337982 x1 y1)). Qed.
Lemma lem1337985 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term10 x1 y1) = (treal_le x1 y1).
Proof. exact (EQ_MP (@lem1337984 x1 y1) (@lem1337975 x1 y1)). Qed.
