
;; Jensen-Shannon Divergence (JSD) function
;; Converts C++ jsd function to MeTTa
(=(jsd $l_tv $r_tv)(
    let* (
        ($bins 10)                                     ;; static int bins = 100
        ($l_bd (mk_distribution_jsd $l_tv))                 ;; BetaDistribution l_bd(l_tv)
        ($r_bd (mk_distribution_jsd $r_tv))                     ;; BetaDistribution r_bd(r_tv)
        ($l_cdf (beta_cdf $l_bd $bins))
        ($r_cdf (beta_cdf $r_bd $bins))
        ($m_cdf (avrg_cdf $l_cdf $r_cdf))              ;; m_cdf = avrg_cdf(l_cdf, r_cdf)
        ($ld (kld $l_cdf $m_cdf))                      ;; ld = kld(l_cdf, m_cdf)
        ($rd (kld $r_cdf $m_cdf))                      ;; rd = kld(r_cdf, m_cdf)
        ($avg (avrg $ld $rd))                          ;; avrg(ld, rd)
    )
    (sqrt-math $avg)                                         ;; return sqrt(avrg(ld, rd))
))


