package game_objects;

import behavior.Explodable;
import core.Game;
import events.ExplodeEvent;

public class Bomb extends GameObject implements Explodable {
	
	protected /*@ spec_public @*/ static final double TIME_TO_EXPLODE = 3000;
	private /*@ spec_public @*/ double timeElapsed; 
	
	private /*@ spec_public @*/ boolean started;
	
	private /*@ spec_public @*/ int flameLevel;
	private /*@ spec_public @*/ int playerNumber;
	
	private /*@ spec_public @*/ Player player;
	
	private /*@ spec_public @*/ boolean exploded;
	
	//@ public invariant timeElapsed < TIME_TO_EXPLODE;
	//@ public invariant flameLevel > 0;
	//por padrao playernNumber e player sao not null
	
	/*@also
	 @ assignable flameLevel;
	 @ assignable playerNumber;
	 @ assignable timeElapsed;
	 @ assignable player;
	 @ ensures this.flameLevel == flameLevel;
	 @ ensures this.playerNumber == playerNumber;
	 @ ensures this.timeElapsed == 0;
	 @ ensures this.player == player;
	 @*/
	public Bomb(Game game, int flameLevel, Player player) {
		super(game, player.getX(), player.getY());
		this.flameLevel = flameLevel;
		this.playerNumber = player.getNumber();
		timeElapsed = 0;
		
		this.player = player;
		
		setExploded(false);
	}
	
	public void explode() {
		if (isExploded())
			return;
		
		System.out.println("Exploding " + this);
		
		Map map = getGame().getMap();
		boolean blockedLeft = false;
		boolean blockedRight = false;
		boolean blockedUp = false;
		boolean blockedDown = false;
		
		setExploded(true);
		checkPosition(getX(), getY());
		
	
		//explode center
		getGame().addObject(new Explosion(getGame(), getX() , getY(), this));	
		System.out.println("exploding at x: "+getX()+" y: "+getY());
		
		for(int i = 1; i <= flameLevel; i++){
			//expand left
			if (getX() - i < 0 || blockedLeft)
				System.out.println("IGNORE");
			else{
				for(int j = 0; j < map.objAt(getX() -i, getY()).length; j++){
					if( map.objAt(getX() -i, getY())[j] instanceof Block )
						blockedLeft = true;
				}
				getGame().addObject(new Explosion(getGame(), getX() - i, getY(), this));
				
				checkPosition(getX() - i, getY());
			}
			//expand right
			if(getX() + i >= map.getWidth() || blockedRight)
				System.out.println("IGNORE");
			else{
				for(int j = 0; j < map.objAt(getX() +i, getY()).length; j++){
					if( map.objAt(getX() +i, getY())[j] instanceof Block )
						blockedRight = true;
				}
				getGame().addObject(new Explosion(getGame(), getX() + i, getY(), this));

				checkPosition(getX() + i, getY());
			}
			
			//expand up
			if (getY() - i < 0 || blockedUp)
				System.out.println("IGNORE");
			else{
				for(int j = 0; j < map.objAt(getX(), getY() -i).length; j++){
					if( map.objAt(getX(), getY()-i)[j] instanceof Block )
						blockedUp = true;
				}
				getGame().addObject(new Explosion(getGame(), getX() , getY() - i, this));

				checkPosition(getX(), getY() - i);
			}
			//expand down
			if(getY() + i >= map.getHeight() || blockedDown)
				System.out.println("IGNORE");
			else{
				for(int j = 0; j < map.objAt(getX(), getY() +i).length; j++){
					if( map.objAt(getX(), getY() +i)[j] instanceof Block )
						blockedDown = true;
				}
				getGame().addObject(new Explosion(getGame(), getX() , getY() + i, this));
				
				checkPosition(getX(), getY() + i);
			}
			
		}
		player.bombExploded();
		getGame().removeObject(this);
	}

	public int getPlayerNumber() {
		return playerNumber;
	}

	private void checkPosition(int x, int y) {
		GameObject[] affecteds = getGame().getMap().objAt(x, y);
		
		for (GameObject affected: affecteds) {
			if (affected instanceof Explodable) {
				((Explodable) affected).exploded(new ExplodeEvent(playerNumber));
			}
		}
	}

	public void start() {
		started = true;
	}
	
	public String toString() {
		return "Bomb> " + super.toString() + "| flameLevel: " + flameLevel + "; playerNumber: " +
			playerNumber;
	}
	
	public void exploded(ExplodeEvent e) {
		explode();
	}

	public boolean isExploded() {
		return exploded;
	}

	public void setExploded(boolean exploded) {
		this.exploded = exploded;
	}

	public void update(double delta) {
		if (started) {
			timeElapsed += delta * 28;
			
			if (timeElapsed >= TIME_TO_EXPLODE)
				explode();
		}
	}
}
