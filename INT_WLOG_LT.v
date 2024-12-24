Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_WLOG_LT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INT_LT_TOTAL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem2311766 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2311767 (P : type1550) : (term1 P) = (term2 P).
Proof. exact (@lem2311766 (term1 P)). Qed.
Lemma lem2311768 (P : type1550) : (term2 P) = (term1 P).
Proof. exact (SYM (@lem2311767 P)). Qed.
Lemma lem2311769 (P : type1550) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem2311772 (P : type1550) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem2311773 (P : type1550) : term5 P.
Proof. exact (fun h0 : term4 P => @lem2311772 P h0). Qed.
Lemma lem2311774 (P : type1550) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem2311775 (P : type1550) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem2311776 (P : type1550) (h1 : term4 P) (h2 : term5 P) : term4 P.
Proof. exact (@lem2311774 P h2 (@lem2311775 P h1)). Qed.
Lemma lem2311777 (P : type1550) (h1 : term4 P) : term6 P.
Proof. exact (fun h0 : term5 P => @lem2311776 P h1 h0). Qed.
Lemma lem2311778 (P : type1550) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem2311779 (P : type1550) (h1 : term4 P) (h2 : term5 P) : term4 P.
Proof. exact (@lem2311777 P h1 (@lem2311778 P h2)). Qed.
Lemma lem2311780 (P : type1550) (h1 : term5 P) : term5 P.
Proof. exact (fun h0 : term4 P => @lem2311779 P h0 h1). Qed.
Lemma lem2311781 (P : type1550) : term7 P.
Proof. exact (fun h0 : term5 P => @lem2311780 P h0). Qed.
Lemma lem2311784 (P : type1550) : term5 P.
Proof. exact (@lem2311781 P (@lem2311773 P)). Qed.
Lemma lem2311828 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2311829 : term8 = term9.
Proof. exact (@lem2311828 term10). Qed.
Lemma lem2311886 (P : type1550) : (term11 P) = (term11 P).
Proof. exact (eq_refl (term11 P)). Qed.
Lemma lem2311887 (P : type1550) : (term4 P) = (term12 P).
Proof. exact (MK_COMB (@lem2311886 P) (@lem2311829)). Qed.
Lemma lem2311890 : term13 = term14.
Proof. exact (fun_ext (fun P : type1550 => @lem2311887 P)). Qed.
Lemma lem2311891 : (@all (int -> int -> Prop)) = (@all (int -> int -> Prop)).
Proof. exact (eq_refl (@all (int -> int -> Prop))). Qed.
Lemma lem2311900 : term15 = term16.
Proof. exact (MK_COMB (@lem2311891) (@lem2311890)). Qed.
Lemma lem2311909 (y : int) (x : int) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem2311910 (x : int) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : int => @lem2311909 y x)). Qed.
Lemma lem2311911 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2311912 (x : int) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem2311911) (@lem2311910 x)). Qed.
Lemma lem2311913 : term20 = term20.
Proof. exact (fun_ext (fun x : int => @lem2311912 x)). Qed.
Lemma lem2311914 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2311915 : term10 = term10.
Proof. exact (MK_COMB (@lem2311914) (@lem2311913)). Qed.
Lemma lem2311916 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2311917 : term9 = term9.
Proof. exact (MK_COMB (@lem2311916) (@lem2311915)). Qed.
Lemma lem2311918 (P : type1550) (x : int) (y : int) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem2311919 (P : type1550) (x : int) : (term21 P x) = (term21 P x).
Proof. exact (fun_ext (fun y : int => @lem2311918 P x y)). Qed.
Lemma lem2311920 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2311921 (P : type1550) (x : int) : (term22 P x) = (term22 P x).
Proof. exact (MK_COMB (@lem2311920) (@lem2311919 P x)). Qed.
Lemma lem2311922 (P : type1550) : (term23 P) = (term23 P).
Proof. exact (fun_ext (fun x : int => @lem2311921 P x)). Qed.
Lemma lem2311923 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2311924 (P : type1550) : (term24 P) = (term24 P).
Proof. exact (MK_COMB (@lem2311923) (@lem2311922 P)). Qed.
Lemma lem2311929 (P : type1550) (x : int) (y : int) : (term25 P x y) = (term25 P x y).
Proof. exact (eq_refl (term25 P x y)). Qed.
Lemma lem2311930 (P : type1550) (x : int) : (term26 P x) = (term26 P x).
Proof. exact (fun_ext (fun y : int => @lem2311929 P x y)). Qed.
Lemma lem2311931 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2311932 (P : type1550) (x : int) : (term27 P x) = (term27 P x).
Proof. exact (MK_COMB (@lem2311931) (@lem2311930 P x)). Qed.
Lemma lem2311933 (P : type1550) : (term28 P) = (term28 P).
Proof. exact (fun_ext (fun x : int => @lem2311932 P x)). Qed.
Lemma lem2311934 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2311935 (P : type1550) : (term29 P) = (term29 P).
Proof. exact (MK_COMB (@lem2311934) (@lem2311933 P)). Qed.
Lemma lem2311940 (P : type1550) (y : int) (x : int) : ((P x y) = (P y x)) = ((P x y) = (P y x)).
Proof. exact (eq_refl ((P x y) = (P y x))). Qed.
Lemma lem2311941 (P : type1550) (x : int) : (term30 P x) = (term30 P x).
Proof. exact (fun_ext (fun y : int => @lem2311940 P y x)). Qed.
Lemma lem2311942 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2311943 (P : type1550) (x : int) : (term31 P x) = (term31 P x).
Proof. exact (MK_COMB (@lem2311942) (@lem2311941 P x)). Qed.
Lemma lem2311944 (P : type1550) : (term32 P) = (term32 P).
Proof. exact (fun_ext (fun x : int => @lem2311943 P x)). Qed.
Lemma lem2311945 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2311946 (P : type1550) : (term33 P) = (term33 P).
Proof. exact (MK_COMB (@lem2311945) (@lem2311944 P)). Qed.
Lemma lem2311947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2311948 (P : type1550) : (term34 P) = (term34 P).
Proof. exact (MK_COMB (@lem2311947) (@lem2311946 P)). Qed.
Lemma lem2311949 (P : type1550) : (term35 P) = (term35 P).
Proof. exact (MK_COMB (@lem2311948 P) (@lem2311935 P)). Qed.
Lemma lem2311950 (P : type1550) (x : int) : (P x x) = (P x x).
Proof. exact (eq_refl (P x x)). Qed.
Lemma lem2311951 (P : type1550) : (term36 P) = (term36 P).
Proof. exact (fun_ext (fun x : int => @lem2311950 P x)). Qed.
Lemma lem2311952 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2311953 (P : type1550) : (term37 P) = (term37 P).
Proof. exact (MK_COMB (@lem2311952) (@lem2311951 P)). Qed.
Lemma lem2311954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2311955 (P : type1550) : (term38 P) = (term38 P).
Proof. exact (MK_COMB (@lem2311954) (@lem2311953 P)). Qed.
Lemma lem2311956 (P : type1550) : (term39 P) = (term39 P).
Proof. exact (MK_COMB (@lem2311955 P) (@lem2311949 P)). Qed.
Lemma lem2311957 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2311958 (P : type1550) : (term40 P) = (term40 P).
Proof. exact (MK_COMB (@lem2311957) (@lem2311956 P)). Qed.
Lemma lem2311959 (P : type1550) : (term1 P) = (term1 P).
Proof. exact (MK_COMB (@lem2311958 P) (@lem2311924 P)). Qed.
Lemma lem2311960 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2311961 (P : type1550) : (term3 P) = (term3 P).
Proof. exact (MK_COMB (@lem2311960) (@lem2311959 P)). Qed.
Lemma lem2311962 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2311963 (P : type1550) : (term11 P) = (term11 P).
Proof. exact (MK_COMB (@lem2311962) (@lem2311961 P)). Qed.
Lemma lem2311964 (P : type1550) : (term12 P) = (term12 P).
Proof. exact (MK_COMB (@lem2311963 P) (@lem2311917)). Qed.
Lemma lem2311965 : term14 = term14.
Proof. exact (fun_ext (fun P : type1550 => @lem2311964 P)). Qed.
Lemma lem2311966 : (@all (int -> int -> Prop)) = (@all (int -> int -> Prop)).
Proof. exact (eq_refl (@all (int -> int -> Prop))). Qed.
Lemma lem2311967 : term16 = term16.
Proof. exact (MK_COMB (@lem2311966) (@lem2311965)). Qed.
Lemma lem2312044 : term15 = term16.
Proof. exact (TRANS (@lem2311900) (@lem2311967)). Qed.
Lemma lem2312045 : term16 = term15.
Proof. exact (SYM (@lem2312044)). Qed.
Lemma lem2312046 (P : type1550) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem2312047 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem2312048 (P : type1550) (x : int) : (P x x) = (P x x).
Proof. exact (eq_refl (P x x)). Qed.
Lemma lem2312049 (P : type1550) : (term36 P) = (term36 P).
Proof. exact (fun_ext (fun x : int => @lem2312048 P x)). Qed.
Lemma lem2312050 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312051 (P : type1550) : (term37 P) = (term37 P).
Proof. exact (MK_COMB (@lem2312050) (@lem2312049 P)). Qed.
Lemma lem2312066 (P : type1550) (y : int) (x : int) : ((P x y) = (P y x)) = (term41 P y x).
Proof. exact (@lem17784 (P x y) (P y x)). Qed.
Lemma lem2312067 (P : type1550) (x : int) : (term30 P x) = (term42 P x).
Proof. exact (fun_ext (fun y : int => @lem2312066 P y x)). Qed.
Lemma lem2312068 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312069 (P : type1550) (x : int) : (term31 P x) = (term43 P x).
Proof. exact (MK_COMB (@lem2312068) (@lem2312067 P x)). Qed.
Lemma lem2312070 (P : type1550) : (term32 P) = (term44 P).
Proof. exact (fun_ext (fun x : int => @lem2312069 P x)). Qed.
Lemma lem2312071 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312072 (P : type1550) : (term33 P) = (term45 P).
Proof. exact (MK_COMB (@lem2312071) (@lem2312070 P)). Qed.
Lemma lem2312079 (P : type1550) (x : int) (y : int) : (term25 P x y) = (term46 P x y).
Proof. exact (@lem17265 (int_lt x y) (P x y)). Qed.
Lemma lem2312080 (P : type1550) (x : int) : (term26 P x) = (term47 P x).
Proof. exact (fun_ext (fun y : int => @lem2312079 P x y)). Qed.
Lemma lem2312081 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312082 (P : type1550) (x : int) : (term27 P x) = (term48 P x).
Proof. exact (MK_COMB (@lem2312081) (@lem2312080 P x)). Qed.
Lemma lem2312083 (P : type1550) : (term28 P) = (term49 P).
Proof. exact (fun_ext (fun x : int => @lem2312082 P x)). Qed.
Lemma lem2312084 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312085 (P : type1550) : (term29 P) = (term50 P).
Proof. exact (MK_COMB (@lem2312084) (@lem2312083 P)). Qed.
Lemma lem2312086 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2312087 (P : type1550) : (term34 P) = (term51 P).
Proof. exact (MK_COMB (@lem2312086) (@lem2312072 P)). Qed.
Lemma lem2312088 (P : type1550) : (term35 P) = (term52 P).
Proof. exact (MK_COMB (@lem2312087 P) (@lem2312085 P)). Qed.
Lemma lem2312089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2312090 (P : type1550) : (term38 P) = (term38 P).
Proof. exact (MK_COMB (@lem2312089) (@lem2312051 P)). Qed.
Lemma lem2312091 (P : type1550) : (term39 P) = (term53 P).
Proof. exact (MK_COMB (@lem2312090 P) (@lem2312088 P)). Qed.
Lemma lem2312093 (P : int -> Prop) : (term54 P) = (term55 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2312094 (P : type1550) (x : int) : (term56 P x) = (term57 P x).
Proof. exact (@lem2312093 (term21 P x)). Qed.
Lemma lem2312095 (P : type1550) (x : int) (y : int) : (term58 P x y) = (P x y).
Proof. exact (eq_refl (term58 P x y)). Qed.
Lemma lem2312096 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2312098 (P : type1550) (x : int) (y : int) : (term59 P x y) = (term60 P x y).
Proof. exact (MK_COMB (@lem2312096) (@lem2312095 P x y)). Qed.
Lemma lem2312099 (P : type1550) (x : int) : (term61 P x) = (term62 P x).
Proof. exact (fun_ext (fun y : int => @lem2312098 P x y)). Qed.
Lemma lem2312100 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2312101 (P : type1550) (x : int) : (term57 P x) = (term63 P x).
Proof. exact (MK_COMB (@lem2312100) (@lem2312099 P x)). Qed.
Lemma lem2312102 (P : type1550) (x : int) : (term56 P x) = (term63 P x).
Proof. exact (TRANS (@lem2312094 P x) (@lem2312101 P x)). Qed.
Lemma lem2312103 (P : int -> Prop) : (term54 P) = (term55 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2312104 (P : type1550) : (term64 P) = (term65 P).
Proof. exact (@lem2312103 (term23 P)). Qed.
Lemma lem2312105 (P : type1550) (x : int) : (term66 P x) = (term22 P x).
Proof. exact (eq_refl (term66 P x)). Qed.
Lemma lem2312106 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2312107 (P : type1550) (x : int) : (term67 P x) = (term56 P x).
Proof. exact (MK_COMB (@lem2312106) (@lem2312105 P x)). Qed.
Lemma lem2312108 (P : type1550) (x : int) : (term67 P x) = (term63 P x).
Proof. exact (TRANS (@lem2312107 P x) (@lem2312102 P x)). Qed.
Lemma lem2312109 (P : type1550) : (term68 P) = (term69 P).
Proof. exact (fun_ext (fun x : int => @lem2312108 P x)). Qed.
Lemma lem2312110 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2312111 (P : type1550) : (term65 P) = (term70 P).
Proof. exact (MK_COMB (@lem2312110) (@lem2312109 P)). Qed.
Lemma lem2312112 (P : type1550) : (term64 P) = (term70 P).
Proof. exact (TRANS (@lem2312104 P) (@lem2312111 P)). Qed.
Lemma lem2312113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2312114 (P : type1550) : (term71 P) = (term72 P).
Proof. exact (MK_COMB (@lem2312113) (@lem2312091 P)). Qed.
Lemma lem2312115 (P : type1550) : (term73 P) = (term74 P).
Proof. exact (MK_COMB (@lem2312114 P) (@lem2312112 P)). Qed.
Lemma lem2312116 (P : type1550) : (term3 P) = (term73 P).
Proof. exact (@lem17362 (term39 P) (term24 P)). Qed.
Lemma lem2312117 (P : type1550) : (term3 P) = (term74 P).
Proof. exact (TRANS (@lem2312116 P) (@lem2312115 P)). Qed.
Lemma lem2312127 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2312128 (P : int -> Prop) (Q : int -> Prop) : (term77 P Q) = (term78 P Q).
Proof. exact (@lem2312127 int P Q). Qed.
Lemma lem2312129 (P : type1550) (x : int) : (term79 P x) = (term80 P x).
Proof. exact (@lem2312128 (term81 P x) (term82 P x)). Qed.
Lemma lem2312130 (P : type1550) (y : int) (x : int) : (term83 P x y) = (term84 P y x).
Proof. exact (eq_refl (term83 P x y)). Qed.
Lemma lem2312131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2312132 (P : type1550) (y : int) (x : int) : (term85 P x y) = (term86 P y x).
Proof. exact (MK_COMB (@lem2312131) (@lem2312130 P y x)). Qed.
Lemma lem2312133 (P : type1550) (y : int) (x : int) : (term87 P x y) = (term88 P y x).
Proof. exact (eq_refl (term87 P x y)). Qed.
Lemma lem2312134 (P : type1550) (y : int) (x : int) : (term89 P x y) = (term41 P y x).
Proof. exact (MK_COMB (@lem2312132 P y x) (@lem2312133 P y x)). Qed.
Lemma lem2312135 (P : type1550) (x : int) : (term90 P x) = (term42 P x).
Proof. exact (fun_ext (fun y : int => @lem2312134 P y x)). Qed.
Lemma lem2312136 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312137 (P : type1550) (x : int) : (term79 P x) = (term43 P x).
Proof. exact (MK_COMB (@lem2312136) (@lem2312135 P x)). Qed.
Lemma lem2312138 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2312139 (P : type1550) (x : int) : (term91 P x) = (term92 P x).
Proof. exact (MK_COMB (@lem2312138) (@lem2312137 P x)). Qed.
Lemma lem2312140 (P : type1550) (y : int) (x : int) : (term83 P x y) = (term84 P y x).
Proof. exact (eq_refl (term83 P x y)). Qed.
Lemma lem2312141 (P : type1550) (x : int) : (term93 P x) = (term81 P x).
Proof. exact (fun_ext (fun y : int => @lem2312140 P y x)). Qed.
Lemma lem2312142 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312143 (P : type1550) (x : int) : (term94 P x) = (term95 P x).
Proof. exact (MK_COMB (@lem2312142) (@lem2312141 P x)). Qed.
Lemma lem2312144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2312145 (P : type1550) (x : int) : (term96 P x) = (term97 P x).
Proof. exact (MK_COMB (@lem2312144) (@lem2312143 P x)). Qed.
Lemma lem2312146 (P : type1550) (y : int) (x : int) : (term87 P x y) = (term88 P y x).
Proof. exact (eq_refl (term87 P x y)). Qed.
Lemma lem2312147 (P : type1550) (x : int) : (term98 P x) = (term82 P x).
Proof. exact (fun_ext (fun y : int => @lem2312146 P y x)). Qed.
Lemma lem2312148 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312149 (P : type1550) (x : int) : (term99 P x) = (term100 P x).
Proof. exact (MK_COMB (@lem2312148) (@lem2312147 P x)). Qed.
Lemma lem2312150 (P : type1550) (x : int) : (term80 P x) = (term101 P x).
Proof. exact (MK_COMB (@lem2312145 P x) (@lem2312149 P x)). Qed.
Lemma lem2312151 (P : type1550) (x : int) : ((term79 P x) = (term80 P x)) = ((term43 P x) = (term101 P x)).
Proof. exact (MK_COMB (@lem2312139 P x) (@lem2312150 P x)). Qed.
Lemma lem2312152 (P : type1550) (x : int) : (term43 P x) = (term101 P x).
Proof. exact (EQ_MP (@lem2312151 P x) (@lem2312129 P x)). Qed.
Lemma lem2312249 (P : type1550) : (term44 P) = (term102 P).
Proof. exact (fun_ext (fun x : int => @lem2312152 P x)). Qed.
Lemma lem2312250 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312251 (P : type1550) : (term45 P) = (term103 P).
Proof. exact (MK_COMB (@lem2312250) (@lem2312249 P)). Qed.
Lemma lem2312253 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem2312254 (P : int -> Prop) (Q : int -> Prop) : (term77 P Q) = (term78 P Q).
Proof. exact (@lem2312253 int P Q). Qed.
Lemma lem2312255 (P : type1550) : (term104 P) = (term105 P).
Proof. exact (@lem2312254 (term106 P) (term107 P)). Qed.
Lemma lem2312256 (P : type1550) (x : int) : (term108 P x) = (term95 P x).
Proof. exact (eq_refl (term108 P x)). Qed.
Lemma lem2312257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2312258 (P : type1550) (x : int) : (term109 P x) = (term97 P x).
Proof. exact (MK_COMB (@lem2312257) (@lem2312256 P x)). Qed.
Lemma lem2312259 (P : type1550) (x : int) : (term110 P x) = (term100 P x).
Proof. exact (eq_refl (term110 P x)). Qed.
Lemma lem2312260 (P : type1550) (x : int) : (term111 P x) = (term101 P x).
Proof. exact (MK_COMB (@lem2312258 P x) (@lem2312259 P x)). Qed.
Lemma lem2312261 (P : type1550) : (term112 P) = (term102 P).
Proof. exact (fun_ext (fun x : int => @lem2312260 P x)). Qed.
Lemma lem2312262 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312263 (P : type1550) : (term104 P) = (term103 P).
Proof. exact (MK_COMB (@lem2312262) (@lem2312261 P)). Qed.
Lemma lem2312264 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2312265 (P : type1550) : (term113 P) = (term114 P).
Proof. exact (MK_COMB (@lem2312264) (@lem2312263 P)). Qed.
Lemma lem2312266 (P : type1550) (x : int) : (term108 P x) = (term95 P x).
Proof. exact (eq_refl (term108 P x)). Qed.
Lemma lem2312267 (P : type1550) : (term115 P) = (term106 P).
Proof. exact (fun_ext (fun x : int => @lem2312266 P x)). Qed.
Lemma lem2312268 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312269 (P : type1550) : (term116 P) = (term117 P).
Proof. exact (MK_COMB (@lem2312268) (@lem2312267 P)). Qed.
Lemma lem2312270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2312271 (P : type1550) : (term118 P) = (term119 P).
Proof. exact (MK_COMB (@lem2312270) (@lem2312269 P)). Qed.
Lemma lem2312272 (P : type1550) (x : int) : (term110 P x) = (term100 P x).
Proof. exact (eq_refl (term110 P x)). Qed.
Lemma lem2312273 (P : type1550) : (term120 P) = (term107 P).
Proof. exact (fun_ext (fun x : int => @lem2312272 P x)). Qed.
Lemma lem2312274 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312275 (P : type1550) : (term121 P) = (term122 P).
Proof. exact (MK_COMB (@lem2312274) (@lem2312273 P)). Qed.
Lemma lem2312276 (P : type1550) : (term105 P) = (term123 P).
Proof. exact (MK_COMB (@lem2312271 P) (@lem2312275 P)). Qed.
Lemma lem2312277 (P : type1550) : ((term104 P) = (term105 P)) = ((term103 P) = (term123 P)).
Proof. exact (MK_COMB (@lem2312265 P) (@lem2312276 P)). Qed.
Lemma lem2312278 (P : type1550) : (term103 P) = (term123 P).
Proof. exact (EQ_MP (@lem2312277 P) (@lem2312255 P)). Qed.
Lemma lem2312383 (P : type1550) : (term45 P) = (term123 P).
Proof. exact (TRANS (@lem2312251 P) (@lem2312278 P)). Qed.
Lemma lem2312384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2312385 (P : type1550) : (term51 P) = (term124 P).
Proof. exact (MK_COMB (@lem2312384) (@lem2312383 P)). Qed.
Lemma lem2312438 (P : type1550) : (term50 P) = (term50 P).
Proof. exact (eq_refl (term50 P)). Qed.
Lemma lem2312439 (P : type1550) : (term52 P) = (term125 P).
Proof. exact (MK_COMB (@lem2312385 P) (@lem2312438 P)). Qed.
Lemma lem2312440 (P : type1550) : (term38 P) = (term38 P).
Proof. exact (eq_refl (term38 P)). Qed.
Lemma lem2312441 (P : type1550) : (term53 P) = (term126 P).
Proof. exact (MK_COMB (@lem2312440 P) (@lem2312439 P)). Qed.
Lemma lem2312442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2312443 (P : type1550) : (term72 P) = (term127 P).
Proof. exact (MK_COMB (@lem2312442) (@lem2312441 P)). Qed.
Lemma lem2312452 (P : type1550) : (term70 P) = (term70 P).
Proof. exact (eq_refl (term70 P)). Qed.
Lemma lem2312453 (P : type1550) : (term74 P) = (term128 P).
Proof. exact (MK_COMB (@lem2312443 P) (@lem2312452 P)). Qed.
Lemma lem2312455 {A : Type'} (P : Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem2312456 (P : Prop) (Q : int -> Prop) : (term131 P Q) = (term132 P Q).
Proof. exact (@lem2312455 int P Q). Qed.
Lemma lem2312457 (P : type1550) : (term133 P) = (term134 P).
Proof. exact (@lem2312456 (term126 P) (term69 P)). Qed.
Lemma lem2312458 (P : type1550) (x : int) : (term135 P x) = (term63 P x).
Proof. exact (eq_refl (term135 P x)). Qed.
Lemma lem2312459 (P : type1550) : (term136 P) = (term69 P).
Proof. exact (fun_ext (fun x : int => @lem2312458 P x)). Qed.
Lemma lem2312460 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2312461 (P : type1550) : (term137 P) = (term70 P).
Proof. exact (MK_COMB (@lem2312460) (@lem2312459 P)). Qed.
Lemma lem2312462 (P : type1550) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem2312463 (P : type1550) : (term133 P) = (term128 P).
Proof. exact (MK_COMB (@lem2312462 P) (@lem2312461 P)). Qed.
Lemma lem2312464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2312465 (P : type1550) : (term138 P) = (term139 P).
Proof. exact (MK_COMB (@lem2312464) (@lem2312463 P)). Qed.
Lemma lem2312466 (P : type1550) (x : int) : (term135 P x) = (term63 P x).
Proof. exact (eq_refl (term135 P x)). Qed.
Lemma lem2312467 (P : type1550) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem2312468 (P : type1550) (x : int) : (term140 P x) = (term141 P x).
Proof. exact (MK_COMB (@lem2312467 P) (@lem2312466 P x)). Qed.
Lemma lem2312469 (P : type1550) : (term142 P) = (term143 P).
Proof. exact (fun_ext (fun x : int => @lem2312468 P x)). Qed.
Lemma lem2312470 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2312471 (P : type1550) : (term134 P) = (term144 P).
Proof. exact (MK_COMB (@lem2312470) (@lem2312469 P)). Qed.
Lemma lem2312472 (P : type1550) : ((term133 P) = (term134 P)) = ((term128 P) = (term144 P)).
Proof. exact (MK_COMB (@lem2312465 P) (@lem2312471 P)). Qed.
Lemma lem2312473 (P : type1550) : (term128 P) = (term144 P).
Proof. exact (EQ_MP (@lem2312472 P) (@lem2312457 P)). Qed.
Lemma lem2312475 {A : Type'} (P : Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem2312476 (P : Prop) (Q : int -> Prop) : (term131 P Q) = (term132 P Q).
Proof. exact (@lem2312475 int P Q). Qed.
Lemma lem2312477 (P : type1550) (x : int) : (term145 P x) = (term146 P x).
Proof. exact (@lem2312476 (term126 P) (term62 P x)). Qed.
Lemma lem2312478 (P : type1550) (x : int) (y : int) : (term147 P x y) = (term60 P x y).
Proof. exact (eq_refl (term147 P x y)). Qed.
Lemma lem2312479 (P : type1550) (x : int) : (term148 P x) = (term62 P x).
Proof. exact (fun_ext (fun y : int => @lem2312478 P x y)). Qed.
Lemma lem2312480 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2312481 (P : type1550) (x : int) : (term149 P x) = (term63 P x).
Proof. exact (MK_COMB (@lem2312480) (@lem2312479 P x)). Qed.
Lemma lem2312482 (P : type1550) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem2312483 (P : type1550) (x : int) : (term145 P x) = (term141 P x).
Proof. exact (MK_COMB (@lem2312482 P) (@lem2312481 P x)). Qed.
Lemma lem2312484 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2312485 (P : type1550) (x : int) : (term150 P x) = (term151 P x).
Proof. exact (MK_COMB (@lem2312484) (@lem2312483 P x)). Qed.
Lemma lem2312486 (P : type1550) (x : int) (y : int) : (term147 P x y) = (term60 P x y).
Proof. exact (eq_refl (term147 P x y)). Qed.
Lemma lem2312487 (P : type1550) : (term127 P) = (term127 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem2312488 (P : type1550) (x : int) (y : int) : (term152 P x y) = (term153 P x y).
Proof. exact (MK_COMB (@lem2312487 P) (@lem2312486 P x y)). Qed.
Lemma lem2312489 (P : type1550) (x : int) : (term154 P x) = (term155 P x).
Proof. exact (fun_ext (fun y : int => @lem2312488 P x y)). Qed.
Lemma lem2312490 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2312491 (P : type1550) (x : int) : (term146 P x) = (term156 P x).
Proof. exact (MK_COMB (@lem2312490) (@lem2312489 P x)). Qed.
Lemma lem2312492 (P : type1550) (x : int) : ((term145 P x) = (term146 P x)) = ((term141 P x) = (term156 P x)).
Proof. exact (MK_COMB (@lem2312485 P x) (@lem2312491 P x)). Qed.
Lemma lem2312493 (P : type1550) (x : int) : (term141 P x) = (term156 P x).
Proof. exact (EQ_MP (@lem2312492 P x) (@lem2312477 P x)). Qed.
Lemma lem2312494 (P : type1550) : (term143 P) = (term157 P).
Proof. exact (fun_ext (fun x : int => @lem2312493 P x)). Qed.
Lemma lem2312495 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2312496 (P : type1550) : (term144 P) = (term158 P).
Proof. exact (MK_COMB (@lem2312495) (@lem2312494 P)). Qed.
Lemma lem2312497 (P : type1550) : (term128 P) = (term158 P).
Proof. exact (TRANS (@lem2312473 P) (@lem2312496 P)). Qed.
Lemma lem2312498 (P : type1550) : (term74 P) = (term158 P).
Proof. exact (TRANS (@lem2312453 P) (@lem2312497 P)). Qed.
Lemma lem2312499 (P : type1550) : (term3 P) = (term158 P).
Proof. exact (TRANS (@lem2312117 P) (@lem2312498 P)). Qed.
Lemma lem2312500 (P : type1550) (h1 : term3 P) : term158 P.
Proof. exact (EQ_MP (@lem2312499 P) (@lem2312046 P h1)). Qed.
Lemma lem2312509 (y : int) (x : int) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem2312510 (x : int) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : int => @lem2312509 y x)). Qed.
Lemma lem2312511 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312512 (x : int) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem2312511) (@lem2312510 x)). Qed.
Lemma lem2312513 : term20 = term20.
Proof. exact (fun_ext (fun x : int => @lem2312512 x)). Qed.
Lemma lem2312514 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312571 : term10 = term10.
Proof. exact (MK_COMB (@lem2312514) (@lem2312513)). Qed.
Lemma lem2312572 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem2312571) (@lem2312047 h1)). Qed.
Lemma lem2312573 (P : type1550) (x : int) (h1 : term156 P x) : term156 P x.
Proof. exact (h1). Qed.
Lemma lem2312574 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term153 P x y.
Proof. exact (h1). Qed.
Lemma lem2312595 (y : int) (x : int) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem2312596 (x : int) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : int => @lem2312595 y x)). Qed.
Lemma lem2312597 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312598 (x : int) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem2312597) (@lem2312596 x)). Qed.
Lemma lem2312599 : term20 = term20.
Proof. exact (fun_ext (fun x : int => @lem2312598 x)). Qed.
Lemma lem2312600 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312601 : term10 = term10.
Proof. exact (MK_COMB (@lem2312600) (@lem2312599)). Qed.
Lemma lem2312602 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem2312601) (@lem2312572 h1)). Qed.
Lemma lem2312609 (P : type1550) (x : int) (y : int) : (term60 P x y) = (term60 P x y).
Proof. exact (eq_refl (term60 P x y)). Qed.
Lemma lem2312624 (P : type1550) (x : int) (y : int) : (term46 P x y) = (term46 P x y).
Proof. exact (eq_refl (term46 P x y)). Qed.
Lemma lem2312625 (P : type1550) (x : int) : (term47 P x) = (term47 P x).
Proof. exact (fun_ext (fun y : int => @lem2312624 P x y)). Qed.
Lemma lem2312626 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312627 (P : type1550) (x : int) : (term48 P x) = (term48 P x).
Proof. exact (MK_COMB (@lem2312626) (@lem2312625 P x)). Qed.
Lemma lem2312628 (P : type1550) : (term49 P) = (term49 P).
Proof. exact (fun_ext (fun x : int => @lem2312627 P x)). Qed.
Lemma lem2312629 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312630 (P : type1550) : (term50 P) = (term50 P).
Proof. exact (MK_COMB (@lem2312629) (@lem2312628 P)). Qed.
Lemma lem2312645 (P : type1550) (y : int) (x : int) : (term88 P y x) = (term88 P y x).
Proof. exact (eq_refl (term88 P y x)). Qed.
Lemma lem2312646 (P : type1550) (x : int) : (term82 P x) = (term82 P x).
Proof. exact (fun_ext (fun y : int => @lem2312645 P y x)). Qed.
Lemma lem2312647 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312648 (P : type1550) (x : int) : (term100 P x) = (term100 P x).
Proof. exact (MK_COMB (@lem2312647) (@lem2312646 P x)). Qed.
Lemma lem2312649 (P : type1550) : (term107 P) = (term107 P).
Proof. exact (fun_ext (fun x : int => @lem2312648 P x)). Qed.
Lemma lem2312650 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312651 (P : type1550) : (term122 P) = (term122 P).
Proof. exact (MK_COMB (@lem2312650) (@lem2312649 P)). Qed.
Lemma lem2312666 (P : type1550) (y : int) (x : int) : (term84 P y x) = (term84 P y x).
Proof. exact (eq_refl (term84 P y x)). Qed.
Lemma lem2312667 (P : type1550) (x : int) : (term81 P x) = (term81 P x).
Proof. exact (fun_ext (fun y : int => @lem2312666 P y x)). Qed.
Lemma lem2312668 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312669 (P : type1550) (x : int) : (term95 P x) = (term95 P x).
Proof. exact (MK_COMB (@lem2312668) (@lem2312667 P x)). Qed.
Lemma lem2312670 (P : type1550) : (term106 P) = (term106 P).
Proof. exact (fun_ext (fun x : int => @lem2312669 P x)). Qed.
Lemma lem2312671 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312672 (P : type1550) : (term117 P) = (term117 P).
Proof. exact (MK_COMB (@lem2312671) (@lem2312670 P)). Qed.
Lemma lem2312673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2312674 (P : type1550) : (term119 P) = (term119 P).
Proof. exact (MK_COMB (@lem2312673) (@lem2312672 P)). Qed.
Lemma lem2312675 (P : type1550) : (term123 P) = (term123 P).
Proof. exact (MK_COMB (@lem2312674 P) (@lem2312651 P)). Qed.
Lemma lem2312676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2312677 (P : type1550) : (term124 P) = (term124 P).
Proof. exact (MK_COMB (@lem2312676) (@lem2312675 P)). Qed.
Lemma lem2312678 (P : type1550) : (term125 P) = (term125 P).
Proof. exact (MK_COMB (@lem2312677 P) (@lem2312630 P)). Qed.
Lemma lem2312683 (P : type1550) (x : int) : (P x x) = (P x x).
Proof. exact (eq_refl (P x x)). Qed.
Lemma lem2312684 (P : type1550) : (term36 P) = (term36 P).
Proof. exact (fun_ext (fun x : int => @lem2312683 P x)). Qed.
Lemma lem2312685 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312686 (P : type1550) : (term37 P) = (term37 P).
Proof. exact (MK_COMB (@lem2312685) (@lem2312684 P)). Qed.
Lemma lem2312687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2312688 (P : type1550) : (term38 P) = (term38 P).
Proof. exact (MK_COMB (@lem2312687) (@lem2312686 P)). Qed.
Lemma lem2312689 (P : type1550) : (term126 P) = (term126 P).
Proof. exact (MK_COMB (@lem2312688 P) (@lem2312678 P)). Qed.
Lemma lem2312690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2312691 (P : type1550) : (term127 P) = (term127 P).
Proof. exact (MK_COMB (@lem2312690) (@lem2312689 P)). Qed.
Lemma lem2312692 (P : type1550) (x : int) (y : int) : (term153 P x y) = (term153 P x y).
Proof. exact (MK_COMB (@lem2312691 P) (@lem2312609 P x y)). Qed.
Lemma lem2312693 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term153 P x y.
Proof. exact (EQ_MP (@lem2312692 P x y) (@lem2312574 P x y h1)). Qed.
Lemma lem2312695 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term126 P.
Proof. exact (proj1 (@lem2312693 P x y h1)). Qed.
Lemma lem2312696 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term125 P.
Proof. exact (proj2 (@lem2312695 P x y h1)). Qed.
Lemma lem2312697 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term37 P.
Proof. exact (proj1 (@lem2312695 P x y h1)). Qed.
Lemma lem2312698 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term50 P.
Proof. exact (proj2 (@lem2312696 P x y h1)). Qed.
Lemma lem2312699 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term123 P.
Proof. exact (proj1 (@lem2312696 P x y h1)). Qed.
Lemma lem2312700 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term122 P.
Proof. exact (proj2 (@lem2312699 P x y h1)). Qed.
Lemma lem2312715 (y : int) (x : int) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem2312716 (x : int) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : int => @lem2312715 y x)). Qed.
Lemma lem2312717 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312718 (x : int) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem2312717) (@lem2312716 x)). Qed.
Lemma lem2312719 : term20 = term20.
Proof. exact (fun_ext (fun x : int => @lem2312718 x)). Qed.
Lemma lem2312720 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312722 : term10 = term10.
Proof. exact (MK_COMB (@lem2312720) (@lem2312719)). Qed.
Lemma lem2312723 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem2312722) (@lem2312602 h1)). Qed.
Lemma lem2312729 (P : type1550) (x : int) : (P x x) = (P x x).
Proof. exact (eq_refl (P x x)). Qed.
Lemma lem2312730 (P : type1550) : (term36 P) = (term36 P).
Proof. exact (fun_ext (fun x : int => @lem2312729 P x)). Qed.
Lemma lem2312731 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312733 (P : type1550) : (term37 P) = (term37 P).
Proof. exact (MK_COMB (@lem2312731) (@lem2312730 P)). Qed.
Lemma lem2312734 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term37 P.
Proof. exact (EQ_MP (@lem2312733 P) (@lem2312697 P x y h1)). Qed.
Lemma lem2312742 (P : type1550) (x : int) (y : int) : (term46 P x y) = (term46 P x y).
Proof. exact (eq_refl (term46 P x y)). Qed.
Lemma lem2312743 (P : type1550) (x : int) : (term47 P x) = (term47 P x).
Proof. exact (fun_ext (fun y : int => @lem2312742 P x y)). Qed.
Lemma lem2312744 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312745 (P : type1550) (x : int) : (term48 P x) = (term48 P x).
Proof. exact (MK_COMB (@lem2312744) (@lem2312743 P x)). Qed.
Lemma lem2312746 (P : type1550) : (term49 P) = (term49 P).
Proof. exact (fun_ext (fun x : int => @lem2312745 P x)). Qed.
Lemma lem2312747 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312749 (P : type1550) : (term50 P) = (term50 P).
Proof. exact (MK_COMB (@lem2312747) (@lem2312746 P)). Qed.
Lemma lem2312750 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term50 P.
Proof. exact (EQ_MP (@lem2312749 P) (@lem2312698 P x y h1)). Qed.
Lemma lem2312774 (P : type1550) (y : int) (x : int) : (term88 P y x) = (term88 P y x).
Proof. exact (eq_refl (term88 P y x)). Qed.
Lemma lem2312775 (P : type1550) (x : int) : (term82 P x) = (term82 P x).
Proof. exact (fun_ext (fun y : int => @lem2312774 P y x)). Qed.
Lemma lem2312776 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312777 (P : type1550) (x : int) : (term100 P x) = (term100 P x).
Proof. exact (MK_COMB (@lem2312776) (@lem2312775 P x)). Qed.
Lemma lem2312778 (P : type1550) : (term107 P) = (term107 P).
Proof. exact (fun_ext (fun x : int => @lem2312777 P x)). Qed.
Lemma lem2312779 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2312781 (P : type1550) : (term122 P) = (term122 P).
Proof. exact (MK_COMB (@lem2312779) (@lem2312778 P)). Qed.
Lemma lem2312782 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term122 P.
Proof. exact (EQ_MP (@lem2312781 P) (@lem2312700 P x y h1)). Qed.
Lemma lem2312783 (_28953 : int) (h1 : term10) : term159 _28953.
Proof. exact (@lem2312723 h1 _28953). Qed.
Lemma lem2312784 (_28953 : int) : (term159 _28953) = (term19 _28953).
Proof. exact (eq_refl (term159 _28953)). Qed.
Lemma lem2312785 (_28953 : int) (h1 : term10) : term19 _28953.
Proof. exact (EQ_MP (@lem2312784 _28953) (@lem2312783 _28953 h1)). Qed.
Lemma lem2312786 (_28953 : int) (_28954 : int) (h1 : term10) : term160 _28953 _28954.
Proof. exact (@lem2312785 _28953 h1 _28954). Qed.
Lemma lem2312787 (_28954 : int) (_28953 : int) : (term160 _28953 _28954) = (term17 _28954 _28953).
Proof. exact (eq_refl (term160 _28953 _28954)). Qed.
Lemma lem2312789 (_28955 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term161 P _28955.
Proof. exact (@lem2312734 P x y h1 _28955). Qed.
Lemma lem2312790 (P : type1550) (_28955 : int) : (term161 P _28955) = (P _28955 _28955).
Proof. exact (eq_refl (term161 P _28955)). Qed.
Lemma lem2312792 (_28956 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term162 P _28956.
Proof. exact (@lem2312750 P x y h1 _28956). Qed.
Lemma lem2312793 (P : type1550) (_28956 : int) : (term162 P _28956) = (term48 P _28956).
Proof. exact (eq_refl (term162 P _28956)). Qed.
Lemma lem2312794 (_28956 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term48 P _28956.
Proof. exact (EQ_MP (@lem2312793 P _28956) (@lem2312792 _28956 P x y h1)). Qed.
Lemma lem2312795 (_28956 : int) (_28957 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term163 P _28956 _28957.
Proof. exact (@lem2312794 _28956 P x y h1 _28957). Qed.
Lemma lem2312796 (P : type1550) (_28956 : int) (_28957 : int) : (term163 P _28956 _28957) = (term46 P _28956 _28957).
Proof. exact (eq_refl (term163 P _28956 _28957)). Qed.
Lemma lem2312804 (_28960 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term110 P _28960.
Proof. exact (@lem2312782 P x y h1 _28960). Qed.
Lemma lem2312805 (P : type1550) (_28960 : int) : (term110 P _28960) = (term100 P _28960).
Proof. exact (eq_refl (term110 P _28960)). Qed.
Lemma lem2312806 (_28960 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term100 P _28960.
Proof. exact (EQ_MP (@lem2312805 P _28960) (@lem2312804 _28960 P x y h1)). Qed.
Lemma lem2312807 (_28960 : int) (_28961 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term87 P _28960 _28961.
Proof. exact (@lem2312806 _28960 P x y h1 _28961). Qed.
Lemma lem2312808 (P : type1550) (_28961 : int) (_28960 : int) : (term87 P _28960 _28961) = (term88 P _28961 _28960).
Proof. exact (eq_refl (term87 P _28960 _28961)). Qed.
Lemma lem2312819 (_28954 : int) (_28953 : int) (h1 : term10) : term17 _28954 _28953.
Proof. exact (EQ_MP (@lem2312787 _28954 _28953) (@lem2312786 _28953 _28954 h1)). Qed.
Lemma lem2312821 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term60 P x y.
Proof. exact (proj2 (@lem2312693 P x y h1)). Qed.
Lemma lem2312829 (_28956 : int) (_28957 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term46 P _28956 _28957.
Proof. exact (EQ_MP (@lem2312796 P _28956 _28957) (@lem2312795 _28956 _28957 P x y h1)). Qed.
Lemma lem2312841 (_28961 : int) (_28960 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term88 P _28961 _28960.
Proof. exact (EQ_MP (@lem2312808 P _28961 _28960) (@lem2312807 _28960 _28961 P x y h1)). Qed.
Lemma lem2312842 (P : type1550) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem2312843 (_28962 : int) (_28964 : int) (h1 : _28962 = _28964) : _28962 = _28964.
Proof. exact (h1). Qed.
Lemma lem2312844 (_28963 : int) (_28965 : int) (h1 : _28963 = _28965) : _28963 = _28965.
Proof. exact (h1). Qed.
Lemma lem2312845 (P : type1550) (_28962 : int) (_28964 : int) (h1 : _28962 = _28964) : (P _28962) = (P _28964).
Proof. exact (MK_COMB (@lem2312842 P) (@lem2312843 _28962 _28964 h1)). Qed.
Lemma lem2312846 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) (h1 : _28962 = _28964) (h2 : _28963 = _28965) : (P _28962 _28963) = (P _28964 _28965).
Proof. exact (MK_COMB (@lem2312845 P _28962 _28964 h1) (@lem2312844 _28963 _28965 h2)). Qed.
Lemma lem2312848 (b : Prop) (a : Prop) : term164 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem2312849 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : term165 _28964 _28965 P _28962 _28963.
Proof. exact (@lem2312848 (P _28964 _28965) (P _28962 _28963)). Qed.
Lemma lem2312850 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) (h1 : _28962 = _28964) (h2 : _28963 = _28965) : term166 _28964 _28965 P _28962 _28963.
Proof. exact (@lem2312849 _28964 _28965 P _28962 _28963 (@lem2312846 P _28962 _28964 _28963 _28965 h1 h2)). Qed.
Lemma lem2312851 (_28965 : int) (P : type1550) (_28963 : int) (_28962 : int) (_28964 : int) (h1 : _28962 = _28964) : term167 _28964 _28965 P _28962 _28963.
Proof. exact (fun h0 : _28963 = _28965 => @lem2312850 P _28962 _28964 _28963 _28965 h1 h0). Qed.
Lemma lem2312853 (a : Prop) (b : Prop) : (a -> b) = (term168 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem2312854 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : (term167 _28964 _28965 P _28962 _28963) = (term169 _28964 _28965 P _28962 _28963).
Proof. exact (@lem2312853 (_28963 = _28965) (term166 _28964 _28965 P _28962 _28963)). Qed.
Lemma lem2312855 (_28965 : int) (P : type1550) (_28963 : int) (_28962 : int) (_28964 : int) (h1 : _28962 = _28964) : term169 _28964 _28965 P _28962 _28963.
Proof. exact (EQ_MP (@lem2312854 _28964 _28965 P _28962 _28963) (@lem2312851 _28965 P _28963 _28962 _28964 h1)). Qed.
Lemma lem2312856 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : term170 _28964 _28965 P _28962 _28963.
Proof. exact (fun h0 : _28962 = _28964 => @lem2312855 _28965 P _28963 _28962 _28964 h0). Qed.
Lemma lem2312858 (a : Prop) (b : Prop) : (a -> b) = (term168 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem2312859 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : (term170 _28964 _28965 P _28962 _28963) = (term171 _28964 _28965 P _28962 _28963).
Proof. exact (@lem2312858 (_28962 = _28964) (term169 _28964 _28965 P _28962 _28963)). Qed.
Lemma lem2312860 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : term171 _28964 _28965 P _28962 _28963.
Proof. exact (EQ_MP (@lem2312859 _28964 _28965 P _28962 _28963) (@lem2312856 _28964 _28965 P _28962 _28963)). Qed.
Lemma lem2312883 (x : int) : x = x.
Proof. exact (@lem21386 int x). Qed.
Lemma lem2312884 (x : int) : term172 x.
Proof. exact (fun h0 : term173 x => @lem2312883 x). Qed.
Lemma lem2312886 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2312887 (x : int) : (term172 x) = (x = x).
Proof. exact (@lem2312886 (x = x)). Qed.
Lemma lem2312888 (x : int) : x = x.
Proof. exact (EQ_MP (@lem2312887 x) (@lem2312884 x)). Qed.
Lemma lem2312891 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) : term60 P x y.
Proof. exact (h1). Qed.
Lemma lem2312892 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) : term175 P x y.
Proof. exact (fun h0 : P x y => @lem2312891 P x y h1). Qed.
Lemma lem2312894 (p : Prop) : (term176 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2312895 (P : type1550) (x : int) (y : int) : (term175 P x y) = (term60 P x y).
Proof. exact (@lem2312894 (P x y)). Qed.
Lemma lem2312896 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) : term60 P x y.
Proof. exact (EQ_MP (@lem2312895 P x y) (@lem2312892 P x y h1)). Qed.
Lemma lem2312898 (_28955 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : P _28955 _28955.
Proof. exact (EQ_MP (@lem2312790 P _28955) (@lem2312789 _28955 P x y h1)). Qed.
Lemma lem2312899 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : P x x.
Proof. exact (@lem2312898 x P x y h1). Qed.
Lemma lem2312900 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term177 P x.
Proof. exact (fun h0 : term178 P x => @lem2312899 P x y h1). Qed.
Lemma lem2312902 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2312903 (P : type1550) (x : int) : (term177 P x) = (P x x).
Proof. exact (@lem2312902 (P x x)). Qed.
Lemma lem2312904 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : P x x.
Proof. exact (EQ_MP (@lem2312903 P x) (@lem2312900 P x y h1)). Qed.
Lemma lem2312922 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2312923 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : (term169 _28964 _28965 P _28962 _28963) = (term180 _28964 _28965 P _28962 _28963).
Proof. exact (@lem2312922 (P _28964 _28965) (term181 _28963 _28965) (term60 P _28962 _28963)). Qed.
Lemma lem2312937 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2312938 (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : (term182 _28965 P _28962 _28963) = (term183 P _28962 _28963 _28965).
Proof. exact (@lem2312937 (term60 P _28962 _28963) (term181 _28963 _28965)). Qed.
Lemma lem2312946 (P : type1550) (_28964 : int) (_28965 : int) : (term184 P _28964 _28965) = (term184 P _28964 _28965).
Proof. exact (eq_refl (term184 P _28964 _28965)). Qed.
Lemma lem2312947 (_28964 : int) (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : (term180 _28964 _28965 P _28962 _28963) = (term185 _28964 P _28962 _28963 _28965).
Proof. exact (MK_COMB (@lem2312946 P _28964 _28965) (@lem2312938 P _28962 _28963 _28965)). Qed.
Lemma lem2312958 (_28964 : int) (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : (term169 _28964 _28965 P _28962 _28963) = (term185 _28964 P _28962 _28963 _28965).
Proof. exact (TRANS (@lem2312923 _28964 _28965 P _28962 _28963) (@lem2312947 _28964 P _28962 _28963 _28965)). Qed.
Lemma lem2312959 (_28962 : int) (_28964 : int) : (term186 _28962 _28964) = (term186 _28962 _28964).
Proof. exact (eq_refl (term186 _28962 _28964)). Qed.
Lemma lem2312960 (_28964 : int) (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : (term171 _28964 _28965 P _28962 _28963) = (term187 _28964 P _28962 _28963 _28965).
Proof. exact (MK_COMB (@lem2312959 _28962 _28964) (@lem2312958 _28964 P _28962 _28963 _28965)). Qed.
Lemma lem2312964 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2312965 (_28964 : int) (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : (term187 _28964 P _28962 _28963 _28965) = (term188 _28964 P _28962 _28963 _28965).
Proof. exact (@lem2312964 (P _28964 _28965) (term181 _28962 _28964) (term183 P _28962 _28963 _28965)). Qed.
Lemma lem2312979 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2312980 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) : (term189 _28964 P _28962 _28963 _28965) = (term190 P _28962 _28964 _28963 _28965).
Proof. exact (@lem2312979 (term60 P _28962 _28963) (term181 _28962 _28964) (term181 _28963 _28965)). Qed.
Lemma lem2313000 (P : type1550) (_28964 : int) (_28965 : int) : (term184 P _28964 _28965) = (term184 P _28964 _28965).
Proof. exact (eq_refl (term184 P _28964 _28965)). Qed.
Lemma lem2313001 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) : (term188 _28964 P _28962 _28963 _28965) = (term191 P _28962 _28964 _28963 _28965).
Proof. exact (MK_COMB (@lem2313000 P _28964 _28965) (@lem2312980 P _28962 _28964 _28963 _28965)). Qed.
Lemma lem2313012 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) : (term187 _28964 P _28962 _28963 _28965) = (term191 P _28962 _28964 _28963 _28965).
Proof. exact (TRANS (@lem2312965 _28964 P _28962 _28963 _28965) (@lem2313001 P _28962 _28964 _28963 _28965)). Qed.
Lemma lem2313013 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) : (term171 _28964 _28965 P _28962 _28963) = (term191 P _28962 _28964 _28963 _28965).
Proof. exact (TRANS (@lem2312960 _28964 P _28962 _28963 _28965) (@lem2313012 P _28962 _28964 _28963 _28965)). Qed.
Lemma lem2313014 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2313015 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) : (term192 _28964 _28965 P _28962 _28963) = (term193 P _28962 _28964 _28963 _28965).
Proof. exact (MK_COMB (@lem2313014) (@lem2313013 P _28962 _28964 _28963 _28965)). Qed.
Lemma lem2313019 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2313020 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : (term194 _28964 _28965 P _28962 _28963) = (term171 _28964 _28965 P _28962 _28963).
Proof. exact (@lem2313019 (term181 _28962 _28964) (term181 _28963 _28965) (term166 _28964 _28965 P _28962 _28963)). Qed.
Lemma lem2313036 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2313037 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : (term169 _28964 _28965 P _28962 _28963) = (term180 _28964 _28965 P _28962 _28963).
Proof. exact (@lem2313036 (P _28964 _28965) (term181 _28963 _28965) (term60 P _28962 _28963)). Qed.
Lemma lem2313051 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2313052 (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : (term182 _28965 P _28962 _28963) = (term183 P _28962 _28963 _28965).
Proof. exact (@lem2313051 (term60 P _28962 _28963) (term181 _28963 _28965)). Qed.
Lemma lem2313060 (P : type1550) (_28964 : int) (_28965 : int) : (term184 P _28964 _28965) = (term184 P _28964 _28965).
Proof. exact (eq_refl (term184 P _28964 _28965)). Qed.
Lemma lem2313061 (_28964 : int) (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : (term180 _28964 _28965 P _28962 _28963) = (term185 _28964 P _28962 _28963 _28965).
Proof. exact (MK_COMB (@lem2313060 P _28964 _28965) (@lem2313052 P _28962 _28963 _28965)). Qed.
Lemma lem2313072 (_28964 : int) (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : (term169 _28964 _28965 P _28962 _28963) = (term185 _28964 P _28962 _28963 _28965).
Proof. exact (TRANS (@lem2313037 _28964 _28965 P _28962 _28963) (@lem2313061 _28964 P _28962 _28963 _28965)). Qed.
Lemma lem2313073 (_28962 : int) (_28964 : int) : (term186 _28962 _28964) = (term186 _28962 _28964).
Proof. exact (eq_refl (term186 _28962 _28964)). Qed.
Lemma lem2313074 (_28964 : int) (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : (term171 _28964 _28965 P _28962 _28963) = (term187 _28964 P _28962 _28963 _28965).
Proof. exact (MK_COMB (@lem2313073 _28962 _28964) (@lem2313072 _28964 P _28962 _28963 _28965)). Qed.
Lemma lem2313078 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2313079 (_28964 : int) (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : (term187 _28964 P _28962 _28963 _28965) = (term188 _28964 P _28962 _28963 _28965).
Proof. exact (@lem2313078 (P _28964 _28965) (term181 _28962 _28964) (term183 P _28962 _28963 _28965)). Qed.
Lemma lem2313093 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2313094 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) : (term189 _28964 P _28962 _28963 _28965) = (term190 P _28962 _28964 _28963 _28965).
Proof. exact (@lem2313093 (term60 P _28962 _28963) (term181 _28962 _28964) (term181 _28963 _28965)). Qed.
Lemma lem2313114 (P : type1550) (_28964 : int) (_28965 : int) : (term184 P _28964 _28965) = (term184 P _28964 _28965).
Proof. exact (eq_refl (term184 P _28964 _28965)). Qed.
Lemma lem2313115 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) : (term188 _28964 P _28962 _28963 _28965) = (term191 P _28962 _28964 _28963 _28965).
Proof. exact (MK_COMB (@lem2313114 P _28964 _28965) (@lem2313094 P _28962 _28964 _28963 _28965)). Qed.
Lemma lem2313126 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) : (term187 _28964 P _28962 _28963 _28965) = (term191 P _28962 _28964 _28963 _28965).
Proof. exact (TRANS (@lem2313079 _28964 P _28962 _28963 _28965) (@lem2313115 P _28962 _28964 _28963 _28965)). Qed.
Lemma lem2313127 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) : (term171 _28964 _28965 P _28962 _28963) = (term191 P _28962 _28964 _28963 _28965).
Proof. exact (TRANS (@lem2313074 _28964 P _28962 _28963 _28965) (@lem2313126 P _28962 _28964 _28963 _28965)). Qed.
Lemma lem2313128 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) : (term194 _28964 _28965 P _28962 _28963) = (term191 P _28962 _28964 _28963 _28965).
Proof. exact (TRANS (@lem2313020 _28964 _28965 P _28962 _28963) (@lem2313127 P _28962 _28964 _28963 _28965)). Qed.
Lemma lem2313129 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) : ((term171 _28964 _28965 P _28962 _28963) = (term194 _28964 _28965 P _28962 _28963)) = ((term191 P _28962 _28964 _28963 _28965) = (term191 P _28962 _28964 _28963 _28965)).
Proof. exact (MK_COMB (@lem2313015 P _28962 _28964 _28963 _28965) (@lem2313128 P _28962 _28964 _28963 _28965)). Qed.
Lemma lem2313131 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2313132 (x : Prop) : (x = x) = True.
Proof. exact (@lem2313131 Prop x). Qed.
Lemma lem2313133 (P : type1550) (_28962 : int) (_28964 : int) (_28963 : int) (_28965 : int) : ((term191 P _28962 _28964 _28963 _28965) = (term191 P _28962 _28964 _28963 _28965)) = True.
Proof. exact (@lem2313132 (term191 P _28962 _28964 _28963 _28965)). Qed.
Lemma lem2313134 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : ((term171 _28964 _28965 P _28962 _28963) = (term194 _28964 _28965 P _28962 _28963)) = True.
Proof. exact (TRANS (@lem2313129 P _28962 _28964 _28963 _28965) (@lem2313133 P _28962 _28964 _28963 _28965)). Qed.
Lemma lem2313135 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : True = ((term171 _28964 _28965 P _28962 _28963) = (term194 _28964 _28965 P _28962 _28963)).
Proof. exact (SYM (@lem2313134 _28964 _28965 P _28962 _28963)). Qed.
Lemma lem2313136 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : (term171 _28964 _28965 P _28962 _28963) = (term194 _28964 _28965 P _28962 _28963).
Proof. exact (EQ_MP (@lem2313135 _28964 _28965 P _28962 _28963) (@lem0)). Qed.
Lemma lem2313137 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : term194 _28964 _28965 P _28962 _28963.
Proof. exact (EQ_MP (@lem2313136 _28964 _28965 P _28962 _28963) (@lem2312860 _28964 _28965 P _28962 _28963)). Qed.
Lemma lem2313139 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2313140 (_28964 : int) (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : (term194 _28964 _28965 P _28962 _28963) = (term196 _28964 P _28962 _28963 _28965).
Proof. exact (@lem2313139 (term197 _28964 _28965 P _28962 _28963) (term181 _28963 _28965)). Qed.
Lemma lem2313142 (a : Prop) (b : Prop) : (term198 a b) = (term199 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2313143 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : (term200 _28964 _28965 P _28962 _28963) = (term201 _28964 _28965 P _28962 _28963).
Proof. exact (@lem2313142 (term181 _28962 _28964) (term166 _28964 _28965 P _28962 _28963)). Qed.
Lemma lem2313145 (a : Prop) : (term202 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2313146 (_28962 : int) (_28964 : int) : (term203 _28962 _28964) = (_28962 = _28964).
Proof. exact (@lem2313145 (_28962 = _28964)). Qed.
Lemma lem2313147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2313148 (_28962 : int) (_28964 : int) : (term204 _28962 _28964) = (term205 _28962 _28964).
Proof. exact (MK_COMB (@lem2313147) (@lem2313146 _28962 _28964)). Qed.
Lemma lem2313150 (a : Prop) (b : Prop) : (term198 a b) = (term199 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2313151 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : (term206 _28964 _28965 P _28962 _28963) = (term207 _28964 _28965 P _28962 _28963).
Proof. exact (@lem2313150 (P _28964 _28965) (term60 P _28962 _28963)). Qed.
Lemma lem2313153 (a : Prop) : (term202 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2313154 (P : type1550) (_28962 : int) (_28963 : int) : (term208 P _28962 _28963) = (P _28962 _28963).
Proof. exact (@lem2313153 (P _28962 _28963)). Qed.
Lemma lem2313155 (P : type1550) (_28964 : int) (_28965 : int) : (term209 P _28964 _28965) = (term209 P _28964 _28965).
Proof. exact (eq_refl (term209 P _28964 _28965)). Qed.
Lemma lem2313156 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : (term207 _28964 _28965 P _28962 _28963) = (term210 _28964 _28965 P _28962 _28963).
Proof. exact (MK_COMB (@lem2313155 P _28964 _28965) (@lem2313154 P _28962 _28963)). Qed.
Lemma lem2313157 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : (term206 _28964 _28965 P _28962 _28963) = (term210 _28964 _28965 P _28962 _28963).
Proof. exact (TRANS (@lem2313151 _28964 _28965 P _28962 _28963) (@lem2313156 _28964 _28965 P _28962 _28963)). Qed.
Lemma lem2313158 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : (term201 _28964 _28965 P _28962 _28963) = (term211 _28964 _28965 P _28962 _28963).
Proof. exact (MK_COMB (@lem2313148 _28962 _28964) (@lem2313157 _28964 _28965 P _28962 _28963)). Qed.
Lemma lem2313159 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : (term200 _28964 _28965 P _28962 _28963) = (term211 _28964 _28965 P _28962 _28963).
Proof. exact (TRANS (@lem2313143 _28964 _28965 P _28962 _28963) (@lem2313158 _28964 _28965 P _28962 _28963)). Qed.
Lemma lem2313160 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2313161 (_28964 : int) (_28965 : int) (P : type1550) (_28962 : int) (_28963 : int) : (term212 _28964 _28965 P _28962 _28963) = (term213 _28964 _28965 P _28962 _28963).
Proof. exact (MK_COMB (@lem2313160) (@lem2313159 _28964 _28965 P _28962 _28963)). Qed.
Lemma lem2313162 (_28963 : int) (_28965 : int) : (term181 _28963 _28965) = (term181 _28963 _28965).
Proof. exact (eq_refl (term181 _28963 _28965)). Qed.
Lemma lem2313163 (_28964 : int) (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : (term196 _28964 P _28962 _28963 _28965) = (term214 _28964 P _28962 _28963 _28965).
Proof. exact (MK_COMB (@lem2313161 _28964 _28965 P _28962 _28963) (@lem2313162 _28963 _28965)). Qed.
Lemma lem2313164 (_28964 : int) (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : (term194 _28964 _28965 P _28962 _28963) = (term214 _28964 P _28962 _28963 _28965).
Proof. exact (TRANS (@lem2313140 _28964 P _28962 _28963 _28965) (@lem2313163 _28964 P _28962 _28963 _28965)). Qed.
Lemma lem2313166 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) (h2 : term153 P x y) : term215 y P x.
Proof. exact (conj (@lem2312896 P x y h1) (@lem2312904 P x y h2)). Qed.
Lemma lem2313167 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) (h2 : term153 P x y) : term216 y P x.
Proof. exact (conj (@lem2312888 x) (@lem2313166 P x y h1 h2)). Qed.
Lemma lem2313169 (_28964 : int) (P : type1550) (_28962 : int) (_28963 : int) (_28965 : int) : term214 _28964 P _28962 _28963 _28965.
Proof. exact (EQ_MP (@lem2313164 _28964 P _28962 _28963 _28965) (@lem2313137 _28964 _28965 P _28962 _28963)). Qed.
Lemma lem2313170 (P : type1550) (x : int) (y : int) : term217 P x y.
Proof. exact (@lem2313169 x P x x y). Qed.
Lemma lem2313173 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) (h2 : term153 P x y) : term181 x y.
Proof. exact (@lem2313170 P x y (@lem2313167 P x y h1 h2)). Qed.
Lemma lem2313174 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) (h2 : term153 P x y) : term218 x y.
Proof. exact (fun h0 : x = y => @lem2313173 P x y h1 h2). Qed.
Lemma lem2313176 (p : Prop) : (term176 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2313177 (x : int) (y : int) : (term218 x y) = (term181 x y).
Proof. exact (@lem2313176 (x = y)). Qed.
Lemma lem2313178 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) (h2 : term153 P x y) : term181 x y.
Proof. exact (EQ_MP (@lem2313177 x y) (@lem2313174 P x y h1 h2)). Qed.
Lemma lem2313181 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) : term60 P x y.
Proof. exact (h1). Qed.
Lemma lem2313182 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) : term175 P x y.
Proof. exact (fun h0 : P x y => @lem2313181 P x y h1). Qed.
Lemma lem2313184 (p : Prop) : (term176 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2313185 (P : type1550) (x : int) (y : int) : (term175 P x y) = (term60 P x y).
Proof. exact (@lem2313184 (P x y)). Qed.
Lemma lem2313186 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) : term60 P x y.
Proof. exact (EQ_MP (@lem2313185 P x y) (@lem2313182 P x y h1)). Qed.
Lemma lem2313188 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2313191 (P : type1550) (_28956 : int) (_28957 : int) : (term46 P _28956 _28957) = (term219 P _28956 _28957).
Proof. exact (@lem2313188 (P _28956 _28957) (term220 _28956 _28957)). Qed.
Lemma lem2313194 (_28956 : int) (_28957 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term219 P _28956 _28957.
Proof. exact (EQ_MP (@lem2313191 P _28956 _28957) (@lem2312829 _28956 _28957 P x y h1)). Qed.
Lemma lem2313195 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term219 P x y.
Proof. exact (@lem2313194 x y P x y h1). Qed.
Lemma lem2313198 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) (h2 : term153 P x y) : term220 x y.
Proof. exact (@lem2313195 P x y h2 (@lem2313186 P x y h1)). Qed.
Lemma lem2313199 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) (h2 : term153 P x y) : term221 x y.
Proof. exact (fun h0 : int_lt x y => @lem2313198 P x y h1 h2). Qed.
Lemma lem2313201 (p : Prop) : (term176 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem2313202 (x : int) (y : int) : (term221 x y) = (term220 x y).
Proof. exact (@lem2313201 (int_lt x y)). Qed.
Lemma lem2313203 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) (h2 : term153 P x y) : term220 x y.
Proof. exact (EQ_MP (@lem2313202 x y) (@lem2313199 P x y h1 h2)). Qed.
Lemma lem2313226 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2313227 (_28953 : int) (_28954 : int) : (term222 _28953 _28954) = (term223 _28953 _28954).
Proof. exact (@lem2313226 (_28953 = _28954) (int_lt _28954 _28953) (int_lt _28953 _28954)). Qed.
Lemma lem2313243 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2313244 (_28954 : int) (_28953 : int) : (term224 _28953 _28954) = (term224 _28954 _28953).
Proof. exact (@lem2313243 (int_lt _28953 _28954) (int_lt _28954 _28953)). Qed.
Lemma lem2313250 (_28953 : int) (_28954 : int) : (term225 _28953 _28954) = (term225 _28953 _28954).
Proof. exact (eq_refl (term225 _28953 _28954)). Qed.
Lemma lem2313251 (_28954 : int) (_28953 : int) : (term223 _28953 _28954) = (term17 _28954 _28953).
Proof. exact (MK_COMB (@lem2313250 _28953 _28954) (@lem2313244 _28954 _28953)). Qed.
Lemma lem2313262 (_28954 : int) (_28953 : int) : (term222 _28953 _28954) = (term17 _28954 _28953).
Proof. exact (TRANS (@lem2313227 _28953 _28954) (@lem2313251 _28954 _28953)). Qed.
Lemma lem2313263 (_28954 : int) (_28953 : int) : (term226 _28954 _28953) = (term226 _28954 _28953).
Proof. exact (eq_refl (term226 _28954 _28953)). Qed.
Lemma lem2313264 (_28954 : int) (_28953 : int) : ((term17 _28954 _28953) = (term222 _28953 _28954)) = ((term17 _28954 _28953) = (term17 _28954 _28953)).
Proof. exact (MK_COMB (@lem2313263 _28954 _28953) (@lem2313262 _28954 _28953)). Qed.
Lemma lem2313266 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2313267 (x : Prop) : (x = x) = True.
Proof. exact (@lem2313266 Prop x). Qed.
Lemma lem2313268 (_28954 : int) (_28953 : int) : ((term17 _28954 _28953) = (term17 _28954 _28953)) = True.
Proof. exact (@lem2313267 (term17 _28954 _28953)). Qed.
Lemma lem2313269 (_28953 : int) (_28954 : int) : ((term17 _28954 _28953) = (term222 _28953 _28954)) = True.
Proof. exact (TRANS (@lem2313264 _28954 _28953) (@lem2313268 _28954 _28953)). Qed.
Lemma lem2313270 (_28953 : int) (_28954 : int) : True = ((term17 _28954 _28953) = (term222 _28953 _28954)).
Proof. exact (SYM (@lem2313269 _28953 _28954)). Qed.
Lemma lem2313271 (_28953 : int) (_28954 : int) : (term17 _28954 _28953) = (term222 _28953 _28954).
Proof. exact (EQ_MP (@lem2313270 _28953 _28954) (@lem0)). Qed.
Lemma lem2313272 (_28953 : int) (_28954 : int) (h1 : term10) : term222 _28953 _28954.
Proof. exact (EQ_MP (@lem2313271 _28953 _28954) (@lem2312819 _28954 _28953 h1)). Qed.
Lemma lem2313274 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2313275 (_28954 : int) (_28953 : int) : (term222 _28953 _28954) = (term227 _28954 _28953).
Proof. exact (@lem2313274 (term228 _28953 _28954) (int_lt _28954 _28953)). Qed.
Lemma lem2313277 (a : Prop) (b : Prop) : (term198 a b) = (term199 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2313278 (_28953 : int) (_28954 : int) : (term229 _28953 _28954) = (term230 _28953 _28954).
Proof. exact (@lem2313277 (_28953 = _28954) (int_lt _28953 _28954)). Qed.
Lemma lem2313279 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2313280 (_28953 : int) (_28954 : int) : (term231 _28953 _28954) = (term232 _28953 _28954).
Proof. exact (MK_COMB (@lem2313279) (@lem2313278 _28953 _28954)). Qed.
Lemma lem2313281 (_28954 : int) (_28953 : int) : (int_lt _28954 _28953) = (int_lt _28954 _28953).
Proof. exact (eq_refl (int_lt _28954 _28953)). Qed.
Lemma lem2313282 (_28954 : int) (_28953 : int) : (term227 _28954 _28953) = (term233 _28954 _28953).
Proof. exact (MK_COMB (@lem2313280 _28953 _28954) (@lem2313281 _28954 _28953)). Qed.
Lemma lem2313283 (_28954 : int) (_28953 : int) : (term222 _28953 _28954) = (term233 _28954 _28953).
Proof. exact (TRANS (@lem2313275 _28954 _28953) (@lem2313282 _28954 _28953)). Qed.
Lemma lem2313285 (P : type1550) (x : int) (y : int) (h1 : term60 P x y) (h2 : term153 P x y) : term230 x y.
Proof. exact (conj (@lem2313178 P x y h1 h2) (@lem2313203 P x y h1 h2)). Qed.
Lemma lem2313287 (_28954 : int) (_28953 : int) (h1 : term10) : term233 _28954 _28953.
Proof. exact (EQ_MP (@lem2313283 _28954 _28953) (@lem2313272 _28953 _28954 h1)). Qed.
Lemma lem2313288 (y : int) (x : int) (h1 : term10) : term233 y x.
Proof. exact (@lem2313287 y x h1). Qed.
Lemma lem2313291 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : int_lt y x.
Proof. exact (@lem2313288 y x h1 (@lem2313285 P x y h2 h3)). Qed.
Lemma lem2313292 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : term234 y x.
Proof. exact (fun h0 : term220 y x => @lem2313291 P x y h1 h2 h3). Qed.
Lemma lem2313294 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2313295 (y : int) (x : int) : (term234 y x) = (int_lt y x).
Proof. exact (@lem2313294 (int_lt y x)). Qed.
Lemma lem2313296 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : int_lt y x.
Proof. exact (EQ_MP (@lem2313295 y x) (@lem2313292 P x y h1 h2 h3)). Qed.
Lemma lem2313302 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2313303 (P : type1550) (_28956 : int) (_28957 : int) : (term46 P _28956 _28957) = (term235 P _28956 _28957).
Proof. exact (@lem2313302 (P _28956 _28957) (term220 _28956 _28957)). Qed.
Lemma lem2313309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2313310 (P : type1550) (_28956 : int) (_28957 : int) : (term236 P _28956 _28957) = (term237 P _28956 _28957).
Proof. exact (MK_COMB (@lem2313309) (@lem2313303 P _28956 _28957)). Qed.
Lemma lem2313316 (P : type1550) (_28956 : int) (_28957 : int) : (term235 P _28956 _28957) = (term235 P _28956 _28957).
Proof. exact (eq_refl (term235 P _28956 _28957)). Qed.
Lemma lem2313317 (P : type1550) (_28956 : int) (_28957 : int) : ((term46 P _28956 _28957) = (term235 P _28956 _28957)) = ((term235 P _28956 _28957) = (term235 P _28956 _28957)).
Proof. exact (MK_COMB (@lem2313310 P _28956 _28957) (@lem2313316 P _28956 _28957)). Qed.
Lemma lem2313319 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2313320 (x : Prop) : (x = x) = True.
Proof. exact (@lem2313319 Prop x). Qed.
Lemma lem2313321 (P : type1550) (_28956 : int) (_28957 : int) : ((term235 P _28956 _28957) = (term235 P _28956 _28957)) = True.
Proof. exact (@lem2313320 (term235 P _28956 _28957)). Qed.
Lemma lem2313322 (P : type1550) (_28956 : int) (_28957 : int) : ((term46 P _28956 _28957) = (term235 P _28956 _28957)) = True.
Proof. exact (TRANS (@lem2313317 P _28956 _28957) (@lem2313321 P _28956 _28957)). Qed.
Lemma lem2313323 (P : type1550) (_28956 : int) (_28957 : int) : True = ((term46 P _28956 _28957) = (term235 P _28956 _28957)).
Proof. exact (SYM (@lem2313322 P _28956 _28957)). Qed.
Lemma lem2313324 (P : type1550) (_28956 : int) (_28957 : int) : (term46 P _28956 _28957) = (term235 P _28956 _28957).
Proof. exact (EQ_MP (@lem2313323 P _28956 _28957) (@lem0)). Qed.
Lemma lem2313325 (_28956 : int) (_28957 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term235 P _28956 _28957.
Proof. exact (EQ_MP (@lem2313324 P _28956 _28957) (@lem2312829 _28956 _28957 P x y h1)). Qed.
Lemma lem2313327 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2313328 (P : type1550) (_28956 : int) (_28957 : int) : (term235 P _28956 _28957) = (term238 P _28956 _28957).
Proof. exact (@lem2313327 (term220 _28956 _28957) (P _28956 _28957)). Qed.
Lemma lem2313330 (a : Prop) : (term202 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2313331 (_28956 : int) (_28957 : int) : (term239 _28956 _28957) = (int_lt _28956 _28957).
Proof. exact (@lem2313330 (int_lt _28956 _28957)). Qed.
Lemma lem2313332 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2313333 (_28956 : int) (_28957 : int) : (term240 _28956 _28957) = (term241 _28956 _28957).
Proof. exact (MK_COMB (@lem2313332) (@lem2313331 _28956 _28957)). Qed.
Lemma lem2313334 (P : type1550) (_28956 : int) (_28957 : int) : (P _28956 _28957) = (P _28956 _28957).
Proof. exact (eq_refl (P _28956 _28957)). Qed.
Lemma lem2313335 (P : type1550) (_28956 : int) (_28957 : int) : (term238 P _28956 _28957) = (term25 P _28956 _28957).
Proof. exact (MK_COMB (@lem2313333 _28956 _28957) (@lem2313334 P _28956 _28957)). Qed.
Lemma lem2313336 (P : type1550) (_28956 : int) (_28957 : int) : (term235 P _28956 _28957) = (term25 P _28956 _28957).
Proof. exact (TRANS (@lem2313328 P _28956 _28957) (@lem2313335 P _28956 _28957)). Qed.
Lemma lem2313339 (_28956 : int) (_28957 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term25 P _28956 _28957.
Proof. exact (EQ_MP (@lem2313336 P _28956 _28957) (@lem2313325 _28956 _28957 P x y h1)). Qed.
Lemma lem2313340 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term25 P y x.
Proof. exact (@lem2313339 y x P x y h1). Qed.
Lemma lem2313343 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : P y x.
Proof. exact (@lem2313340 P x y h3 (@lem2313296 P x y h1 h2 h3)). Qed.
Lemma lem2313344 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : term242 P y x.
Proof. exact (fun h0 : term60 P y x => @lem2313343 P x y h1 h2 h3). Qed.
Lemma lem2313346 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2313347 (P : type1550) (y : int) (x : int) : (term242 P y x) = (P y x).
Proof. exact (@lem2313346 (P y x)). Qed.
Lemma lem2313348 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : P y x.
Proof. exact (EQ_MP (@lem2313347 P y x) (@lem2313344 P x y h1 h2 h3)). Qed.
Lemma lem2313354 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2313355 (P : type1550) (_28960 : int) (_28961 : int) : (term88 P _28961 _28960) = (term84 P _28960 _28961).
Proof. exact (@lem2313354 (P _28961 _28960) (term60 P _28960 _28961)). Qed.
Lemma lem2313361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2313362 (P : type1550) (_28960 : int) (_28961 : int) : (term243 P _28961 _28960) = (term244 P _28960 _28961).
Proof. exact (MK_COMB (@lem2313361) (@lem2313355 P _28960 _28961)). Qed.
Lemma lem2313368 (P : type1550) (_28960 : int) (_28961 : int) : (term84 P _28960 _28961) = (term84 P _28960 _28961).
Proof. exact (eq_refl (term84 P _28960 _28961)). Qed.
Lemma lem2313369 (P : type1550) (_28960 : int) (_28961 : int) : ((term88 P _28961 _28960) = (term84 P _28960 _28961)) = ((term84 P _28960 _28961) = (term84 P _28960 _28961)).
Proof. exact (MK_COMB (@lem2313362 P _28960 _28961) (@lem2313368 P _28960 _28961)). Qed.
Lemma lem2313371 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2313372 (x : Prop) : (x = x) = True.
Proof. exact (@lem2313371 Prop x). Qed.
Lemma lem2313373 (P : type1550) (_28960 : int) (_28961 : int) : ((term84 P _28960 _28961) = (term84 P _28960 _28961)) = True.
Proof. exact (@lem2313372 (term84 P _28960 _28961)). Qed.
Lemma lem2313374 (P : type1550) (_28960 : int) (_28961 : int) : ((term88 P _28961 _28960) = (term84 P _28960 _28961)) = True.
Proof. exact (TRANS (@lem2313369 P _28960 _28961) (@lem2313373 P _28960 _28961)). Qed.
Lemma lem2313375 (P : type1550) (_28960 : int) (_28961 : int) : True = ((term88 P _28961 _28960) = (term84 P _28960 _28961)).
Proof. exact (SYM (@lem2313374 P _28960 _28961)). Qed.
Lemma lem2313376 (P : type1550) (_28960 : int) (_28961 : int) : (term88 P _28961 _28960) = (term84 P _28960 _28961).
Proof. exact (EQ_MP (@lem2313375 P _28960 _28961) (@lem0)). Qed.
Lemma lem2313377 (_28960 : int) (_28961 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term84 P _28960 _28961.
Proof. exact (EQ_MP (@lem2313376 P _28960 _28961) (@lem2312841 _28961 _28960 P x y h1)). Qed.
Lemma lem2313379 (b : Prop) (a : Prop) : (a \/ b) = (term195 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2313380 (P : type1550) (_28961 : int) (_28960 : int) : (term84 P _28960 _28961) = (term245 P _28961 _28960).
Proof. exact (@lem2313379 (term60 P _28960 _28961) (P _28961 _28960)). Qed.
Lemma lem2313382 (a : Prop) : (term202 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2313383 (P : type1550) (_28960 : int) (_28961 : int) : (term208 P _28960 _28961) = (P _28960 _28961).
Proof. exact (@lem2313382 (P _28960 _28961)). Qed.
Lemma lem2313384 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2313385 (P : type1550) (_28960 : int) (_28961 : int) : (term246 P _28960 _28961) = (term247 P _28960 _28961).
Proof. exact (MK_COMB (@lem2313384) (@lem2313383 P _28960 _28961)). Qed.
Lemma lem2313386 (P : type1550) (_28961 : int) (_28960 : int) : (P _28961 _28960) = (P _28961 _28960).
Proof. exact (eq_refl (P _28961 _28960)). Qed.
Lemma lem2313387 (P : type1550) (_28961 : int) (_28960 : int) : (term245 P _28961 _28960) = (term248 P _28961 _28960).
Proof. exact (MK_COMB (@lem2313385 P _28960 _28961) (@lem2313386 P _28961 _28960)). Qed.
Lemma lem2313388 (P : type1550) (_28961 : int) (_28960 : int) : (term84 P _28960 _28961) = (term248 P _28961 _28960).
Proof. exact (TRANS (@lem2313380 P _28961 _28960) (@lem2313387 P _28961 _28960)). Qed.
Lemma lem2313391 (_28961 : int) (_28960 : int) (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term248 P _28961 _28960.
Proof. exact (EQ_MP (@lem2313388 P _28961 _28960) (@lem2313377 _28960 _28961 P x y h1)). Qed.
Lemma lem2313392 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term248 P x y.
Proof. exact (@lem2313391 x y P x y h1). Qed.
Lemma lem2313395 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term60 P x y) (h3 : term153 P x y) : P x y.
Proof. exact (@lem2313392 P x y h3 (@lem2313348 P x y h1 h2 h3)). Qed.
Lemma lem2313396 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term153 P x y) : term242 P x y.
Proof. exact (fun h0 : term60 P x y => @lem2313395 P x y h1 h0 h2). Qed.
Lemma lem2313398 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2313399 (P : type1550) (x : int) (y : int) : (term242 P x y) = (P x y).
Proof. exact (@lem2313398 (P x y)). Qed.
Lemma lem2313400 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term153 P x y) : P x y.
Proof. exact (EQ_MP (@lem2313399 P x y) (@lem2313396 P x y h1 h2)). Qed.
Lemma lem2313403 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2313405 (P : type1550) (x : int) (y : int) : (term60 P x y) = (term249 P x y).
Proof. exact (@lem2313403 (P x y)). Qed.
Lemma lem2313408 (P : type1550) (x : int) (y : int) (h1 : term153 P x y) : term249 P x y.
Proof. exact (EQ_MP (@lem2313405 P x y) (@lem2312821 P x y h1)). Qed.
Lemma lem2313411 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term153 P x y) : False.
Proof. exact (@lem2313408 P x y h2 (@lem2313400 P x y h1 h2)). Qed.
Lemma lem2313412 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term153 P x y) : term250.
Proof. exact (fun h0 : ~ False => @lem2313411 P x y h1 h2). Qed.
Lemma lem2313414 (p : Prop) : (term174 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2313415 : term250 = False.
Proof. exact (@lem2313414 False). Qed.
Lemma lem2313416 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term153 P x y) : False.
Proof. exact (EQ_MP (@lem2313415) (@lem2313412 P x y h1 h2)). Qed.
Lemma lem2313417 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term153 P x y) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem2313416 P x y h1 h2) (fun h3 : False => @lem2312723 h1)). Qed.
Lemma lem2313418 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term153 P x y) : False.
Proof. exact (EQ_MP (@lem2313417 P x y h1 h2) (@lem2312723 h1)). Qed.
Lemma lem2313419 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term153 P x y) : (term153 P x y) = False.
Proof. exact (prop_ext (fun h3 : term153 P x y => @lem2313418 P x y h1 h2) (fun h3 : False => @lem2312693 P x y h2)). Qed.
Lemma lem2313420 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term153 P x y) : False.
Proof. exact (EQ_MP (@lem2313419 P x y h1 h2) (@lem2312693 P x y h2)). Qed.
Lemma lem2313421 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term153 P x y) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem2313420 P x y h1 h2) (fun h3 : False => @lem2312602 h1)). Qed.
Lemma lem2313422 (P : type1550) (x : int) (y : int) (h1 : term10) (h2 : term153 P x y) : False.
Proof. exact (EQ_MP (@lem2313421 P x y h1 h2) (@lem2312602 h1)). Qed.
Lemma lem2313423 (P : type1550) (x : int) (h1 : term10) (h2 : term156 P x) : False.
Proof. exact (ex_elim (@lem2312573 P x h2) (fun y : int => fun h0 : term155 P x y => @lem2313422 P x y h1 h0)). Qed.
Lemma lem2313424 (P : type1550) (h1 : term10) (h2 : term3 P) : False.
Proof. exact (ex_elim (@lem2312500 P h2) (fun x : int => fun h0 : term157 P x => @lem2313423 P x h1 h0)). Qed.
Lemma lem2313425 (P : type1550) (h1 : term10) (h2 : term3 P) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem2313424 P h1 h2) (fun h3 : False => @lem2312572 h1)). Qed.
Lemma lem2313426 (P : type1550) (h1 : term10) (h2 : term3 P) : False.
Proof. exact (EQ_MP (@lem2313425 P h1 h2) (@lem2312572 h1)). Qed.
Lemma lem2313427 (P : type1550) (h1 : term3 P) : term8.
Proof. exact (fun h0 : term10 => @lem2313426 P h0 h1). Qed.
Lemma lem2313428 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem2313429 (P : type1550) (h1 : term3 P) : term9.
Proof. exact (EQ_MP (@lem2313428) (@lem2313427 P h1)). Qed.
Lemma lem2313430 (P : type1550) : term12 P.
Proof. exact (fun h0 : term3 P => @lem2313429 P h0). Qed.
Lemma lem2313435 : term16.
Proof. exact (fun P : type1550 => @lem2313430 P). Qed.
Lemma lem2313436 : term15.
Proof. exact (EQ_MP (@lem2312045) (@lem2313435)). Qed.
Lemma lem2313437 (P : type1550) : term251 P.
Proof. exact (@lem2313436 P). Qed.
Lemma lem2313438 (P : type1550) : (term251 P) = (term4 P).
Proof. exact (eq_refl (term251 P)). Qed.
Lemma lem2313439 (P : type1550) : term4 P.
Proof. exact (EQ_MP (@lem2313438 P) (@lem2313437 P)). Qed.
Lemma lem2313441 (P : type1550) : term4 P.
Proof. exact (@lem2311784 P (@lem2313439 P)). Qed.
Lemma lem2313442 (P : type1550) (h1 : term3 P) : term8.
Proof. exact (@lem2313441 P (@lem2311769 P h1)). Qed.
Lemma lem2313443 (P : type1550) (h1 : term3 P) : False.
Proof. exact (@lem2313442 P h1 (@lem2305063)). Qed.
Lemma lem2313444 (P : type1550) (h1 : term3 P) : (term3 P) = False.
Proof. exact (prop_ext (fun h2 : term3 P => @lem2313443 P h1) (fun h2 : False => @lem2311769 P h1)). Qed.
Lemma lem2313445 (P : type1550) (h1 : term3 P) : False.
Proof. exact (EQ_MP (@lem2313444 P h1) (@lem2311769 P h1)). Qed.
Lemma lem2313446 (P : type1550) : term2 P.
Proof. exact (fun h0 : term3 P => @lem2313445 P h0). Qed.
Lemma lem2313447 (P : type1550) : term1 P.
Proof. exact (EQ_MP (@lem2311768 P) (@lem2313446 P)). Qed.
