package game_objects;


import behavior.Explodable;
import behavior.MoveListener;
import constants.Constants.Movement;
import core.Game;
import events.ExplodeEvent;
import events.MoveEvent;

public class Player extends GameObject implements Explodable {
	private static final long BOMB_COOLDOWN_NS = 0;
	private static final long BLOCK_COOLDOWN_NS = 0;
	private static final double MOVE_TIMEOUT = 50;
	
	private double moveTimer = 0;
	
	private long lastBomb = 0;
	private long lastBlock = 0;
	
	private int number;
	
	private int speed;
	
	private int flameLevel;
	private int maxBombs;
	private int activeBombs;
		
	private MoveListener moveListener;
	
	//STATES
	private boolean movingLeft;
	private boolean movingRight;
	private boolean movingUp;
	private boolean movingDown;
	private boolean stopped;
	private boolean dead;

	public Player(Game game, int x, int y, int number) {
		super(game, x, y);
		this.number = number;
		
		flameLevel = 3;
		maxBombs = 3;
		activeBombs = 0;
		
		trepassable = true;
		this.moveListener = game.getMap();
	}
	
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
	
	public void bombExploded(){
		activeBombs--;
	}
	
	@Override
	public void exploded(ExplodeEvent e) {
		dead = true;
		System.out.println("Player #" + number + " has been killed by player #" + e.getPlayerNumber());
	}

	public int getNumber() {
		return number;
	}

	public boolean isDead() {
		return dead;
	}
	
	public void move(boolean[] move) {
		movingUp = move[0];
		movingDown = move[1];
		movingLeft = move[2];
		movingRight = move[3];
	}

	@Override
	public String toString() {
		return "Player> " + super.toString() + "; playerNumber: " +
				number;
	}

	@Override
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
