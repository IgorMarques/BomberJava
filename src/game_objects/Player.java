package game_objects;


import behavior.Explodable;
import behavior.MoveListener;
import constants.Constants.Movement;
import core.Game;
import events.ExplodeEvent;
import events.MoveEvent;

public class Player extends GameObject implements Explodable {
	private /*@ spec_public @*/ static final long BOMB_COOLDOWN_NS = 0;
	//@ public invariant BOMB_COOLDOWN_NS == 0;

	private /*@ spec_public @*/ static final double MOVE_TIMEOUT = 50;
	//@ public invariant MOVE_TIMEOUT == 50;
	
	private /*@ spec_public @*/ double moveTimer = 0;
	//@ public initially moveTimer == 0;
	
	private /*@ spec_public @*/ long lastBomb = 0;
	//@ public initially lastBomb == 0;
	
	private /*@ spec_public @*/ int number;
	
	private /*@ spec_public @*/ int speed;
	
	private /*@ spec_public @*/ int flameLevel;
	private /*@ spec_public @*/ int maxBombs;
	private /*@ spec_public @*/ int activeBombs;
		
	private /*@ spec_public @*/ MoveListener moveListener;
	
	//STATES
	private /*@ spec_public @*/ boolean movingLeft;
	private /*@ spec_public @*/ boolean movingRight;
	private /*@ spec_public @*/ boolean movingUp;
	private  /*@ spec_public @*/ boolean movingDown;
	private /*@ spec_public @*/ boolean stopped;
	private /*@ spec_public @*/ boolean dead;
	
	//@ public invariant maxBombs >= activeBombs;

	/*@ also
	 @ assignable this.number;
	 @ assignable this.flameLevel;
	 @ assignable this.maxBombs;
	 @ assignable this.activeBombs;
	 @ assignable this.trepassable;
	 @ assignable this.moveListener;
	 @ ensures this.number == number;
	 @ ensures this.flameLevel == 3;
	 @ ensures this.activeBombs == 0;
	 @ ensures this.maxBombs == 3;
	 @ ensures this.trepassable == true;
	 @ ensures this.moveListener == game.getMap();
	 @*/
	public Player(Game game, int x, int y, int number) {
		super(game, x, y);
		this.number = number;
		
		flameLevel = 3;
		maxBombs = 3;
		activeBombs = 0;
		
		trepassable = true;
		this.moveListener = game.getMap();
	}
	
	/*@ requires this.maxBombs > activeBombs;
	 @ requires !(System.nanoTime() - lastBomb < BOMB_COOLDOWN_NS);
	 @ requires (getGame().getMap().isMovableSpace(bombToAdd.getX(), bombToAdd.getY())) {
				getGame().addObject(bombToAdd);
	 @ assignable activeBombs;
	 @ ensures
	 @	public constraint activeBombs == \old(activeBombs)+1;
	 @  ensures \exists Bomb bomb; bomb == Bomb(getGame(), flameLevel, this); bombToAdd.getX() == getX(), bombToAdd.getY()== getY();
	 @*/
	public void placeBomb() {
		if (maxBombs > activeBombs){
			long now = System.nanoTime();
			
			if (now - lastBomb < BOMB_COOLDOWN_NS)
				return;
			
			lastBomb = System.nanoTime();
					
			Bomb bombToAdd = new Bomb(getGame(), flameLevel, this);
			
			if (getGame().getMap().isMovableSpace(bombToAdd.getX(), bombToAdd.getY())) {
				getGame().addObject(bombToAdd);
				bombToAdd.start();
				activeBombs++;
				System.out.println("Placed bomb at " + bombToAdd.getX() + ", " + bombToAdd.getY());
			}
		}
	}
	
	/*@ requires true;
	@ assignable this.activeBombs;
	@ public constraint
	@ 	ensures activeBombs == \old(activeBombs) -1;
	@ */
	public void bombExploded(){
		activeBombs--;
	}
	
	/*@ requires true;
	@ assignable dead;
	@ ensures dead == true;
	@ */
	public void exploded(ExplodeEvent e) {
		dead = true;
		System.out.println("Player #" + number + " has been killed by player #" + e.getPlayerNumber());
	}

	/*@ requires true;
	@ assignable \nothing;
	@ ensures \result == this.number;
	@ */
	public /*@pure@*/ int getNumber() {
		return number;
	}

	/*@ requires true;
	@ assignable \nothing;
	@ ensures \result == this.dead;
	@ */
	public /*@pure@*/ boolean isDead() {
		return dead;
	}
	
	/*@ requires move.length == 4;
	@ assignable movingUp;
	@ assignable movingDown;
	@ assignable movingLeft;
	@ assignable movingRight;
	@ ensures movingUp == move [0];
	@ ensures movingDown == move [1];
	@ ensures movingLeft == move [2];
	@ ensures movingRight == move [3];
	@ */
	public void move(boolean[] move) {
		movingUp = move[0];
		movingDown = move[1];
		movingLeft = move[2];
		movingRight = move[3];
	}

	/*@ requires true;
	 @ assignable \nothing;
	 @ ensures \result ==" Player> " + super.toString() + "; playerNumber: " +
				number ;
	 @*/
	public /*@pure@*/ String toString() {
		return "Player> " + super.toString() + "; playerNumber: " +
				number;
	}

	/*@ requires delta > -1;
	@ assignable x;
	@ assignable y;
	@ assignable moveTimer;
	@ ensures moveTimer == (moveTimer + 28 * delta);
	@ ensures checkMove(x,y);
	@ also
	@ requires movingDown
	@ public constraint
	@ 	ensures y == \old(y) + 1;
	@ also
	@ requires movingLeft
	@ public constraint
	@ 	ensures x == \old(x) - 1;
	@ also
	@ requires movingUp
	@ public constraint
	@ 	ensures y == \old(y) - 1;
	@ also
	@ requires movingRight
	@ public constraint
	@ ensures x == \old(x) + 1;
	@ */
	public void update(double delta) {
		int x = getX(), y = getY();
		
		if (movingDown) {
			y += 1;
		} 
		
		if (movingUp) {
			y -= 1;
		} 
		
		if (movingLeft) {
			x -= 1;
		} 
		
		if (movingRight) {
			x += 1;
		} 

		if (stopped){
			moveTimer = 0;
			return;
		}
		
		moveTimer = (moveTimer + 28 * delta);
		checkMove(x, y);
	}

	private void checkMove(int x, int y) {
		int lastX = this.getX();
		int lastY = this.getY();
		
		if (moveTimer > MOVE_TIMEOUT) {
			moveTimer %= MOVE_TIMEOUT;
			
			if (getGame().getMap().isValid(x, y)) {
				setX(x);
				setY(y);
				
				if (x != lastX && y != lastY)
					moveListener.objectMoved(new MoveEvent(lastX, lastY, this));
			}
		}
	}
}
