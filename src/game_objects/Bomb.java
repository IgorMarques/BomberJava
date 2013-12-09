package game_objects;

import behavior.Explodable;
import core.Game;
import events.ExplodeEvent;
import static constants.Constants.WIDTH;
import static constants.Constants.HEIGHT;

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
	 	 nao anotei o explodable como assignable por ele já estar anotado no setExploded
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
	
	/*@ 	requires isExploded == true;
	  @		assingnable \nothing
	  @		ensures \nothing
	  @	also
	  @		requires isExploded ==false;
	  @		assignable getGame();
	  		nao anotei player como assignable por ele já estar anotado
	  @ 	ensures 
	  @			map.objAt(getX(), getY()) instanceof Explosion;
	  @ 		\forall int i; 1 <=i && i  < flameleval();
	  @				map.objAt(getX()+i, getY()) instanceof Explosion;
	  @				map.objAt(getX()-i, getY()) instanceof Explosion;
	  @				map.objAt(getX(), getY()+i) instanceof Explosion;
	  @				map.objAt(getX(), getY()-i) instanceof Explosion;
	  @ also
	  @ 	ensures (
	  @ 		\forall int i; 0 <=i && i  <getGame().getObjects().length;
	  @				getGame().getObjects()[i] != this;
	  @		) 
	  @		public constraint
	  @     	ensures \old(getGame().getObjects().length)-1 == getGame().getObjects.length
	@*/

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

	/*@ requires true;
	 @ assignable \nothing;
	 @ ensures \result == playerNumber; 
	 @ */
	public /*@pure@*/ int getPlayerNumber() {
		return playerNumber;
	}
	
	/*@ requires x < WIDTH;
	 @ requires y < HEIGHT;
	 @ assignable \nothing;
	 @ ensures \forall int i; 0 <=i && i  < getGame().getMap().objAt(x, y);
	 @				requires getGame().getMap().objAt(x, y)[i] instanceof Explodable;
	 @				assignbale getGame().getMap().objAt(x, y)[i];
	 @				ensures getGame().getMap().objAt(x, y)[i].exploded();
	 @ */
	private void checkPosition(int x, int y) {
		GameObject[] affecteds = getGame().getMap().objAt(x, y);
		
		for (GameObject affected: affecteds) {
			if (affected instanceof Explodable) {
				((Explodable) affected).exploded(new ExplodeEvent(playerNumber));
			}
		}
	}

	/*@ requires true;
	 @ assignable started;
	 @ ensures started == true;
	 */
	public void start() {
		started = true;
	}
	
	/*@ also 
	 	@ ensures \result == "Bomb> " + super.toString() + "| flameLevel: " + flameLevel + "; playerNumber: " +
			playerNumber;
	 @*/
	 public String toString() {
		return "Bomb> " + super.toString() + "| flameLevel: " + flameLevel + "; playerNumber: " +
			playerNumber;
	}
	
	/*@ requires true;
	 @ assignable nothing;
	 @ ensures explode();
	 */
	public void exploded(ExplodeEvent e) {
		explode();
	}

	/*@ requires true;
	 @ assignable nothing;
	 @ ensures \result == exploded;
	 */
	public /*@pure@*/ boolean isExploded() {
		return exploded;
	}

	/*@ requires true;
	 @ assignable exploded;
	 @ ensures this.exploded == exploded;@*/
	public void setExploded(boolean exploded) {
		this.exploded = exploded;
	}

	/*@ requires delta > 0;
	 @ requires started == true
	 @ assignable timeElapsed;
	 @ ensures timeElapsed += delta * 28;
	 @ also
	 @ requires timeElapsed >= TIME_TO_EXPLODE;
	 @ ensures explode();
	@*/
	public void update(double delta) {
		if (started) {
			timeElapsed += delta * 28;
			
			if (timeElapsed >= TIME_TO_EXPLODE)
				explode();
		}
	}
}
