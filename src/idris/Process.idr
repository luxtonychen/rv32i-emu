module Process
import Linear
import LinContext

record Process p_in w_in p_out ctx where
  constructor P
  fwd_fn: LinContext p_in ctx -@ LinContext p_out ctx
  write_fn: LinContext w_in ctx -@ LinContext () ctx
