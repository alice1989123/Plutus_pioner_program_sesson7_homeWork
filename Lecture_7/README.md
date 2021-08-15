# Plutus_pioner_program_sesson7_homeWork 
This week the assignment was to  modify the previous game explained in lecture 7  to a Rock Paper Scissor Game

Lecture https://www.youtube.com/watch?v=uwZ903Zd0DU.

link to full course:  https://github.com/input-output-hk/plutus-pioneer-program.

The logic is as follows: in the On chain code I modify the check so that it only checks if the nonce an reveling choice of the reveal is honestly in case of a redeemer of type Reveal by player 1.

Then the check logic of state machine changed so that depending if of the choices of both players when validating a reveal redeemer the player 1 can claim back all Stake or only the half dependig if he won or its a tie or nothing if he lost. When player 1 claims the stake corresponding to a tie ( half of the Stake) if changes the gameDatum byte-string to empty byte-sting, so that the offchain Code of player 2 can know it was a tie. Then off-Chain code has the cording modification to Loggin the correct events.

