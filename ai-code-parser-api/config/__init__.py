from flask import Flask

def create_app():
    app = Flask(__name__)
    
    # Load configuration settings
    app.config.from_object('config.settings')

    # Register blueprints for routes
    from app.routes import debugging, nlp, formal
    app.register_blueprint(debugging.bp)
    app.register_blueprint(nlp.bp)
    app.register_blueprint(formal.bp)

    return app